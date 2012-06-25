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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#include <tsvc.h>
#include <tee-sdk/tzmarshal.h>
#include <tee-sdk/svcapi.h>

#include <trustvisor/tv_utpm.h>

#include "sha1.h"
#include "libarb.h"
#include "dbg.h"

/**
 * TODO: Split this into two C files: those that need to touch global
 * variables, and those that do not.
 */

#define MAX_NV_SIZE (5*SHA_DIGEST_LENGTH)

arb_internal_state_t g_arb_internal_state;

/**
 * (1) serialize both our state and the PAL's state and (2) seal
 * them.
 */
static arb_err_t serialize_and_seal(const arb_internal_state_t *state,
																		uint8_t *new_snapshot,
																		size_t *new_snapshot_len) {
	TPM_PCR_INFO tpmPcrInfo;
	arb_err_t rv;
	size_t size;
	static uint8_t buf[1024]; /* XXX */

	memcpy(buf, state, sizeof(arb_internal_state_t));
	rv = pal_arb_serialize_state(buf + sizeof(arb_internal_state_t),
															 &size);
	if(ARB_ENONE != rv) { return rv; } /* Not sure how to deal with this
																			* one cleanly */
	size += sizeof(arb_internal_state_t);
	/* Now calculate how much space utpm_seal will consume given size inputs */
	*new_snapshot_len = utpm_seal_output_size(size, /* XXX */false);
	/* seal size bytes from buf into new_snapshot */
	/* XXX Don't select any PCRs for now! */
	memset(&tpmPcrInfo, 0, sizeof(TPM_PCR_INFO));

	log_hex("serialize_and_seal [arb_internal|pal]_state_t: ",
					buf, size);
	if(0 != svc_utpm_seal(&tpmPcrInfo, buf, size, new_snapshot, new_snapshot_len)) {
		return ARB_EBADCMD;
	}

	return rv;
}

/**
 * TODO: Flesh out with full PRNG.  Initialize with uTPM entropy.
 */
arb_err_t arb_initialize_internal_state(uint8_t *new_snapshot,
																				size_t *new_snapshot_len) {
  size_t size;
  uint8_t nvbuf[MAX_NV_SIZE];
	arb_err_t rv;

	/* Just compute how much space is needed for the new
	 * snapshot. Doesn't depend on 'state' right now but could in the
	 * future. */
	if(!new_snapshot && new_snapshot_len) {
		pal_arb_serialize_state(NULL, new_snapshot_len); /* XXX ignoring return */
		*new_snapshot_len += sizeof(arb_internal_state_t);
		*new_snapshot_len = utpm_seal_output_size(*new_snapshot_len, /* XXX use PCRs! */false);
		return ARB_ENONE;
	}

	if(!new_snapshot || !new_snapshot_len) {
		return ARB_EPARAM;
	}
	
	/**
	 * Seed PRNG.
	 */
  if(svc_utpm_rand_block(
       (uint8_t*)&g_arb_internal_state.dummy_prng_state,
       sizeof(g_arb_internal_state.dummy_prng_state))
     != 0) {
    return ARB_ETZ; /* TODO: collect TZ error and "shift it on" */
  }

	/**
	 * Set HistorySummary_0 = 0
	 */
	memset(&g_arb_internal_state.history_summary, 0,
				 sizeof(g_arb_internal_state.history_summary));

  /* Zeroize HistorySummary in NVRAM */
  if(svc_tpmnvram_getsize(&size)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }
	log_info("svc_tpmnvram_getsize() says size = %d", size);
	
  if(size < SHA_DIGEST_LENGTH || size > MAX_NV_SIZE) {
    return ARB_ENOMEM;
  }  

	memset(nvbuf, 0, size);
  
  if(svc_tpmnvram_writeall(nvbuf)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  /**
	 * Now (1) initialize the PAL's state, (2) serialize both our state
	 * and the PAL's state, (3) seal them, and (4) output it.
	 */

	rv = pal_arb_initialize_state();
	if(ARB_ENONE != rv) { return rv; }

	rv = serialize_and_seal(&g_arb_internal_state, new_snapshot, new_snapshot_len);
	
  return rv;
}

/**
 * Assumption: history summary already determined not to be current.
 *
 * Returns: true if replay is needed to recover from crash. false
 * otherwise.
 */
static bool arb_is_replay_needed(const uint8_t alleged_history_summary[ARB_HIST_SUM_LEN],
                                 const uint8_t *request,
                                 size_t request_len,
                                 const uint8_t nvram[ARB_HIST_SUM_LEN]) {
  SHA_CTX ctx;
  uint8_t digest[SHA_DIGEST_LENGTH];

  COMPILE_TIME_ASSERT(SHA_DIGEST_LENGTH == ARB_HIST_SUM_LEN);

	log_hex("alleged_history_summary: ", alleged_history_summary, ARB_HIST_SUM_LEN);
	log_hex("request:                 ", request, request_len);

  SHA1_Init(&ctx);
  SHA1_Update(&ctx, alleged_history_summary, ARB_HIST_SUM_LEN);
  SHA1_Update(&ctx, request, request_len);
  SHA1_Final(digest, &ctx);

	log_hex("digest: ", digest, SHA_DIGEST_LENGTH);
	log_hex("nvram:  ", nvram, ARB_HIST_SUM_LEN);

  return 0 == memcmp(digest, nvram, ARB_HIST_SUM_LEN);
}

/**
 * This function is called to update NVRAM in preparation to execute
 * the latest request.
 */
static arb_err_t arb_update_history_summary(const uint8_t *request, /* in */
                                            uint32_t request_len, /* in */
																						uint8_t history_summary[ARB_HIST_SUM_LEN]) /* out */
{
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

  if(0 != memcmp(history_summary, nvbuf, ARB_HIST_SUM_LEN)) {
    /* This is FATAL and should never happen; it should be an
     * ASSERT!!! The legitimate need for recovery should have been
     * discovered prior to a call to this function. */
		log_err("FATAL: 0 != memcmp(history_summary, nvbuf, ARB_HIST_SUM_LEN)");
    return ARB_EBADSTATE;
  }

  /**
   * Okay, now actually update the value in NVRAM.
   */
  
  SHA1_Init(&ctx);
  SHA1_Update(&ctx, history_summary, ARB_HIST_SUM_LEN);
  SHA1_Update(&ctx, request, request_len);
  SHA1_Final(nvbuf, &ctx);
  
  if(svc_tpmnvram_writeall(nvbuf)) {
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  /**
   * And if successful, update the history_summary in our own state.
   */
  memcpy(history_summary, nvbuf, ARB_HIST_SUM_LEN);

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
arb_err_t arb_execute_request(bool attempt_recovery,
															const uint8_t *request,
                              size_t request_len,
                              /*const*/ uint8_t *old_snapshot,
                              size_t old_snapshot_len,
															uint8_t *new_snapshot, /* pre-allocated, OUT*/
															size_t *new_snapshot_len) /* IN / OUT */
{
  size_t size;
  uint8_t nvbuf[MAX_NV_SIZE];
	arb_err_t rv;
	TPM_DIGEST digestAtCreation;
	static uint8_t buf[4096];

  if(!request || request_len < sizeof(int) ||
		 !old_snapshot || old_snapshot_len < sizeof(int) ||
		 !new_snapshot
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
	 *
	 * Snapshot = svc_utpm_seal(arb_internal_state_t||serialized_pal_state)
   */

  /* XXX TODO Optimize the common case when we don't have to seal /
   * unseal every request. */
  
	/* TODO: Tighten this bound to detect more errors.  Also check that
	 * data is not insanely huge. Might even be able to use lack of any
	 * UTPM_SEALING_OVERHEAD to indicate whether sealing is
	 * necessary??? */
  if(old_snapshot_len < sizeof(arb_internal_state_t)) {
    return ARB_EPARAM;
  }

	if(0 != svc_utpm_unseal(old_snapshot, old_snapshot_len,
													buf, &size,
													(uint8_t*)&digestAtCreation)) {
		log_err("svc_utpm_unseal FAILED");
		return ARB_EUNSEALFAILED;
	}

	log_hex("unsealed buf: ", buf, size);
	
	/**
	 * Now that we have unsealed, we may have sensitive data in memory.
	 * Be responsible: Zero things upon failure, etc.
	 */	

	/* First comes arb_internal_state_t; copy it */
	memcpy(&g_arb_internal_state, buf, sizeof(arb_internal_state_t));

	log_hex("g_arb_internal_state: ", &g_arb_internal_state,
					sizeof(arb_internal_state_t));
	
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
	 *
	 * Depending on whether we are in (1) or (2), the provided request
	 * will be either new or re-submitted during a recovery attempt.
	 * The boolean attempt_recovery indicates which case we are in.
   */

  if(svc_tpmnvram_getsize(&size)) {
		log_err("svc_tpmnvram_getsize FAILED");
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }

  if(svc_tpmnvram_readall(nvbuf)) {
		log_err("svc_tpmnvram_readall FAILED");
    return (TZ_ERROR_GENERIC << 8) | ARB_ETZ;
  }
  
  /* Validate case (1) */
	if(!attempt_recovery) {
		if(0 == memcmp(g_arb_internal_state.history_summary,
									 nvbuf, ARB_HIST_SUM_LEN)) {
			/* We're good! Update history summary (in g_arb_internal_state and NVRAM) */
			log_info("History summary determined to be current");
			rv = arb_update_history_summary(request, request_len, g_arb_internal_state.history_summary);
			if(ARB_ENONE != rv) {
				log_err("arb_update_history_summary() failed rv = %d", rv);
				return rv;
			}
		} else {
			log_info("Recovery needed.  New transaction aborted.");
			return ARB_ERECOVERYNEEDED;
		}
  }
  /* Check for case (2) */
  else { /* attempt_recovery = true; */
		if(arb_is_replay_needed(
         g_arb_internal_state.history_summary,
         request,
         request_len,
         nvbuf)) {
			/* Something went wrong last time, but we appear to have what it takes to
			 * recover. Just let the transaction run again. */
			log_info("History summary determined to be valid but stale.");
			log_info("Re-executing previous transaction with identical inputs.");
			/* Update history_summary in g_arb_internal_state to match that
			 * already in NVRAM */
			memcpy(g_arb_internal_state.history_summary, nvbuf, ARB_HIST_SUM_LEN);
		} else {
			log_err("History summary INVALID. Recovery impossible! State is WEDGED! Aieeee!");
			return ARB_EWEDGED;
		}
	}

	/**
	 * If we're still here, time to run the transaction, serialize PAL
	 * state, and seal it up for outputting.
	 */

	rv = pal_arb_deserialize_state(buf+sizeof(arb_internal_state_t), size-sizeof(arb_internal_state_t));
	if(ARB_ENONE != rv) {
		log_err("pal_arb_deserialize_state() failed with rv %d", rv);
		return rv;
	}
	
	rv = pal_arb_advance_state(request, request_len);
	if(ARB_ENONE != rv) {
		log_err("pal_arb_advance_state() failed with rv %d", rv);
		return rv;
	}

	rv = serialize_and_seal(&g_arb_internal_state, new_snapshot, new_snapshot_len);
	if(ARB_ENONE != rv) {
		log_err("serialize_and_seal() failed with rv %d", rv);
		return rv;
	}

	log_info("%s: Success!", __FUNCTION__);
	
  return ARB_ENONE;
}


/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* c-basic-offset: 2 */
/* End:             */
