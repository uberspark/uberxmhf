/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

#include <stdint.h>
#include <stdbool.h>

#include <tee-sdk/tzmarshal.h>
#include <tee-sdk/svcapi.h>

#include <trustvisor/tv_utpm.h>

#include "libarb.h"

/* Guessing at seal overhead. TODO: Enhance UTPM to be able to
 * definitively return how much overhead there is. */
#define UTPM_SEALING_OVERHEAD 100 

#define MAX_NV_SIZE (5*SHA_DIGEST_LENGTH)

arb_internal_state_t g_arb_internal_state;

/* Use hideous global buffer to avoid malloc() */
uint8_t g_hideous_buffer[4096];

/**
 * TODO: Flesh out with full PRNG.  Initialize with uTPM entropy.
 */
arb_err_t arb_initialize_internal_state(arb_internal_state_t *state,
																				uint8_t *new_snapshot,
																				uint32_t *new_snapshot_len) {
  unsigned int i;
  size_t size;
  uint8_t nvbuf[MAX_NV_SIZE];
	arb_err_t rv;

	/* Just compute how much space is needed for the new
	 * snapshot. Doesn't depend on 'state' right now but could in the
	 * future. */
	if(!new_snapshot && state && new_snapshot_len) {
		pal_arb_serialize_state(NULL, new_snapshot_len); /* XXX ignoring return */
		*new_snapshot_len += sizeof(arb_internal_state_t);
		*new_snapshot_len += UTPM_SEALING_OVERHEAD;
		return ARB_ENONE;
	}

	if(!state || !new_snapshot || !new_snapshot_len) {
		return ARB_EPARAM;
	}
	
	/**
	 * Seed PRNG.
	 */
  if(svc_utpm_rand_block(
       (uint8_t*)&state->dummy_prng_state,
       sizeof(state->dummy_prng_state))
     != 0) {
    return ARB_ETZ; /* TODO: collect TZ error and "shift it on" */
  }

	/**
	 * Set HistorySummary_0 = 0
	 */
  for(i=0; i<sizeof(state->history_summary); i++) {
    state->history_summary[i] = 0;
  }

  /* Zeroize HistorySummary in NVRAM */
  if(svc_tpmnvram_getsize(&size)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  if(size < SHA_DIGEST_LENGTH || size > MAX_NV_SIZE) {
    return ARB_ENOMEM;
  }  

  for(i=0; i<size; i++) {
    nvbuf[i] = 0; 
  }
  
  if(svc_tpmnvram_writeall(nvbuf)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  /**
	 * Now (1) initialize the PAL's state, (2) serialize both our state
	 * and the PAL's state, (3) seal them, and (4) output it.
	 */

	rv = pal_arb_initialize_state();
	if(ARB_ENONE != rv) { return rv; }

	for(i=0; i<sizeof(arb_internal_state_t); i++) {
		g_hideous_buffer[i] = ((uint8_t*)state)[i];
	}
	rv = pal_arb_serialize_state(g_hideous_buffer + sizeof(arb_internal_state_t),
															 &size);
	if(ARB_ENONE != rv) { return rv; } /* Not sure how to deal with this
																			* one cleanly */
	size += sizeof(arb_internal_state_t);
	
  return ARB_ENONE;
}

/**
 * TODO: Get sane string.h functions in here somehow.
 */
static bool compare(const uint8_t* a, const uint8_t* b, size_t size) {
  size_t i;
  for(i=0; i<size; i++) {
    if(a[i] != b[i]) {
      return false;
    }
  }
  return true;
}

/**
 * Returns: true if current snapshot matches history_summary. false
 * otherwise.
 */
 
static bool arb_is_history_summary_current(uint8_t alleged_history_summary[ARB_HIST_SUM_LEN],
                                           uint8_t nvram[ARB_HIST_SUM_LEN]) {
  return compare(alleged_history_summary, nvram, ARB_HIST_SUM_LEN);
}

/**
 * Assumption: arb_is_snapshot_current() already returned false.
 *
 * Returns: true if replay is needed to recover from crash. false
 * otherwise.
 */
static bool arb_is_replay_needed(uint8_t alleged_history_summary[ARB_HIST_SUM_LEN],
                                 uint8_t request,
                                 uint32_t request_len,
                                 uint8_t nvram[ARB_HIST_SUM_LEN]) {
  SHA_CTX ctx;
  uint8_t digest[SHA_DIGEST_LENGTH];

  /* TODO: Enable this check! */
  /* ASSERT(SHA_DIGEST_LENGTH == ARB_HIST_SUM_LEN); */
  
  SHA1_INIT(&ctx);
  SHA1_Update(&ctx, alleged_history_summary, ARB_HIST_SUM_LEN);
  SHA1_Update(&ctx, request, request_len);
  SHA1_Final(digest, &ctx);

  return compare(digest, nvram, ARB_HIST_SUM_LEN);
}

/**
 * This function is called to update NVRAM in preparation to execute
 * the latest request.
 */
static arb_err_t arb_update_history_summary(const uint8_t *request, /* in */
                                            uint32_t request_len, /* in */
																						uint8_t history_summary[ARB_HIST_SUM_LEN]) /* out */
{
  unsigned int i;
  size_t size;
  uint8_t nvbuf[MAX_NV_SIZE];
  SHA_CTX ctx;

	/* Sanity-check inputs */
	if(!request || request_len < sizeof(int)) {
		return ARB_EPARAM;
	}

	/* Make sure we have a big enough buffer (trying to survive without
	 * malloc) */
  if(svc_tpmnvram_getsize(&size)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  if(size > MAX_NV_SIZE) {
    return ARB_ENOMEM;
  }

  /**
   * Sanity check: current history summary should match current NVRAM
   * value.
   */
  
  if(svc_tpmnvram_readall(nvbuf)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  if(!compare(history_summary, nvbuf,
              ARB_HIST_SUM_LEN)) {
    /* This is FATAL and should never happen; it should be an ASSERT!!! */
    return ARB_EBADSTATE;
  }

  /**
   * Okay, now actually update the value in NVRAM.
   */
  
  SHA1_INIT(&ctx);
  SHA1_Update(&ctx, history_summary, ARB_HIST_SUM_LEN);
  SHA1_Update(&ctx, request, request_len);
  SHA1_Final(nvbuf, &ctx);
  
  if(svc_tpmnvram_writeall(nvbuf)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  return ARB_ENONE;
}

/**
 * Confirm that we are presently in a valid state, and then advance
 * history summary based on new request.  Actual "work" of
 * application-specific request details are handled by the PAL, not
 * here in libarb.
 *
 * "request" is PAL-specific and here we only treat it as an opaque
 * byte string.
 *
 * "old_snapshot" is the sealed, serialized state of both libarb and
 * the PAL itself from the previous run.
 *
 * "new_snapshot" is preallocated space (maximum possible size in
 * *new_snapshot_len) to store the new state snapshot.
 *
 * Not much in the way of failure handling.  Pretty much just bails
 * out with an error code if anything doesn't go perfectly.
 * Definitely not ready for really important data yet.
 */
arb_err_t arb_execute_request(const uint8_t *request,
                              const uint32_t request_len,
                              const uint8_t *old_snapshot,
                              const uint32_t old_snapshot_len,
															uint8_t *new_snapshot, /* pre-allocated, OUT*/
															uint32_t *new_snapshot_len) /* IN / OUT */
{
  size_t size;
  uint8_t nvbuf[MAX_NV_SIZE];
  unsigned int i;
	arb_err_t rv;
  
  if(!request || !snapshot ||
     request_len < sizeof(int)
     /* snapshot_len checked below */
     ) {
    return ARB_EPARAM;
  }

  /**
   * 1. Unseal previous snapshot.
   *
   * If the snapshot was manipulated, it will not unseal properly.  If
   * it unseals, it was a previous snapshot created by this PAL.  We
   * do _not_ yet know if it is fresh.
   */

  /* XXX TODO Optimize the common case when we don't have to seal /
   * unseal every request. For now, we assume snapshot is an encrypted
   * arb_internal_state_t.
   */
  
  if(snapshot_len < sizeof(arb_internal_state_t)) {
    return ARB_EPARAM;
  }

  /* XXX TODO Seal / Unseal the state! Skipping for now to get basic
   * operation stood up so we can test as we go. */
  for(i=0; i<sizeof(arb_internal_state_t); i++) {
    *((uint8_t*)&g_arb_internal_state) = snapshot[i];
  }  

  /* XXX TODO Deserialize previous PAL-specific state */
  
  /**
   * 2. Validate History Summary.
   *
   * Part of the snapshot is the history summary that is relevant for
   * this snapshot.  There are two legitimate possibilities:
   *
   * (1) The HistorySummary stored in NVRAM matches the HistorySummary
   * in the unsealed snapshot.  This is the common case, and
   * everything is fine. Go ahead and update the HistorySummary in
   * NVRAM based on the new request.
   *
   * (2) The HistorySummary stored in NVRAM matches
   * Hash(HistorySummary||Request).  This is the recovery case, after
   * a crash.  Go ahead and redo the request.
   *
   * (WEDGE) If the above cases do not hold, we are under attack or
   * wedged in an "impossible" state.  Give up.
   */


  if(svc_tpmnvram_getsize(&size)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  if(svc_tpmnvram_readall(nvbuf)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }
  
  /* Check for case (1) */
  if(arb_is_history_summary_current(g_arb_internal_state.history_summary,
                                    nvbuf)) {
    /* We're good!  Go ahead and start the new transaction. */
    // 1. Update history summary (in g_arb_internal_state and NVRAM)
    rv = arb_update_history_summary(request, request_len, g_arb_internal_state.history_summary);
    if(ARB_ENONE != rv) { return rv; }
    // 2. Do the actual transaction
    rv = pal_arb_advance_state(request, request_len);
    if(ARB_ENONE != rv) { return rv; }
    rv = pal_arb_serialize_state(serialized_state, serialized_state_len); /* XXX malloc()??? */
    if(ARB_ENONE != rv) { return rv; }
  }
  /* Check for case (2) */
  else if(arb_is_replay_needed(
         g_arb_internal_state.history_summary,
         request,
         request_len,
         nvbuf)) {
    /* Something went wrong last time, but we have what it takes to
     * recover. We must start recovery now. */
    // 1. Don't update history summary since it was updated at the
    //    beginning of the previous, failed transaction.
    // 2. Do the actual transaction
    rv = pal_arb_advance_state(request, request_len);
    if(ARB_ENONE != rv) { return rv; }
    rv = pal_arb_serialize_state(serialized_state, serialized_state_len); /* XXX malloc()??? */
    if(ARB_ENONE != rv) { return rv; }
  }
  /* We're WEDGED.  Lame!!! */
  else {
    return ARB_EWEDGED;
  }
  
  
  return ARB_ENONE;
}


/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* c-basic-offset: 2 */
/* End:             */

