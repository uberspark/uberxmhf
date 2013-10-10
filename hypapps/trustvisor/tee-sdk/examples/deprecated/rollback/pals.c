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

#include <tsvc.h> /* newlib */
#include <tee-sdk/tzmarshal.h>
#include <tee-sdk/svcapi.h>

#include <trustvisor/tv_utpm.h>

#include "libarb.h"
#include "pals.h"
#include "sha1.h"
#include "dbg.h"

/**
 * TODO: Split this into three C files: PAL-specific that need to
 * touch global variables, PAL-specific that do not, and
 * AntiRollBack-specifc.
 */

/**
 * This global variable is needed to isolate PAL-specific state data
 * structures from the general-purpose libarb.  This could probably be
 * cleaned up through the use of function pointers or perhaps just a
 * better design (time will tell).
 */
pal_state_t g_pal_state;

char end[10*4096]; /* shenanigans to provide a heap (libnosys's sbrk) */
static void* get_stderr(size_t *len)
{
  char *rv = malloc(4096);
  if(!rv) {
    return NULL;
  }
  *len = tsvc_read_stderr(rv, 4095);
  rv[*len] = '\0';
  return rv;
}

static void append_stderr(tzi_encode_buffer_t *psOutBuf) 
{
	size_t len;
	void *buf;

	buf = get_stderr(&len);
	if(NULL != buf) {
		/* If len is too long, too bad. */
		TZIEncodeArray(psOutBuf, buf, len);
	}
	free(buf);
}

/**
 * Convention: When something fails, clobber the other output
 * parameters and only output stderr.
 *
 * TODO: Refactor if this capability becomes built-in to tee-sdk or
 * similar.
 *
 * Returns: nothing.  We're in an error situation, there is nowhere
 * else for return values to go.
 */
static void append_only_stderr(tzi_encode_buffer_t *psOutBuf) 
{
	log_err("Internal failure! Above stderr output should aid in diagnosis");

	/* Clobber any previously buffered outputs */
	TZIEncodeBufReInit(psOutBuf);

	append_stderr(psOutBuf);
}

/* Move state from global variable into serialized buffer. If
 * destination buffer is NULL, just populate the _len parameter with
 * how much space would have been needed. serialized_state should
 * already point to enough space. */
arb_err_t pal_arb_serialize_state(OUT uint8_t *serialized_state,
                                  OUT size_t *serialized_state_len) {
	unsigned int i;

	/* Answer a length-only request if one is given. */
	if(!serialized_state && serialized_state_len) {
		*serialized_state_len = sizeof(pal_state_t);
		return ARB_ENONE;
	}
	
	/* Otherwise, normal request. "serialized_state" should have already
	 * been allocated by the caller. */
	if(!serialized_state || !serialized_state_len) {
		return ARB_EPARAM;
	}

	*serialized_state_len = sizeof(pal_state_t);

	for(i=0; i<*serialized_state_len; i++) {
		serialized_state[i] = ((uint8_t*)&g_pal_state)[i];
	}

	return ARB_ENONE;
}

/* Move state from serialized buffer into global variable */
arb_err_t pal_arb_deserialize_state(IN const uint8_t *serialized_state,
                                    IN const size_t serialized_state_len) {
	unsigned int i;
	
	/* State should have already been allocated by the caller. */
	if(!serialized_state || serialized_state_len < 1) {
		log_err("!serialized_state || serialized_state_len < 1");
		return ARB_EPARAM;
	}

	if(serialized_state_len != sizeof(pal_state_t)) {
		log_err("serialized_state_len(%d) != sizeof(pal_state_t)(%d)",
						serialized_state_len, sizeof(pal_state_t));
		log_hex("serialized_state: ", serialized_state, serialized_state_len);
		return ARB_EBADSTATE;
	}

	for(i=0; i<serialized_state_len; i++) {
		((uint8_t*)&g_pal_state)[i] = serialized_state[i];
	}

	log_info("%s: Success!", __FUNCTION__);
	return ARB_ENONE;	
}

arb_err_t pal_arb_initialize_state()
{
	/* Initialization is extremely trivial here. */
	g_pal_state.counter = 0;

	return ARB_ENONE;
}

arb_err_t pal_arb_advance_state(IN const uint8_t *request,
                                IN size_t request_len)
{
	if(!request || request_len < sizeof(int)) {
		return ARB_EPARAM;
	}

	switch(((pal_request_t*)request)->cmd) {
			case PAL_ARB_INCREMENT:
				g_pal_state.counter++;
				break;
			default:
				return ARB_EBADCMDHANDLE;
	}

	return ARB_ENONE;
}

/* TODO: rename this to something better, e.g., pal_entry. */
void pals(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{

	/**
	 * AntiRollBack initialize / execute.
	 */
    
  switch(uiCommand) {
		
	case PAL_ARB_INITIALIZE:
		/**
		 * This command tells the PAL to wipe any previously existing
		 * state and initialize both its own state and the
		 * AntiRollBack-specific internal state.  CAUTION: You can lose
		 * your data by calling this carelessly.  There are no other
		 * inputs. An initial counter value and a state snapshot will be
		 * output.
		 */
	{
		size_t counter_len;
		uint8_t* counter;
		size_t new_snapshot_len;
		uint8_t* new_snapshot;
		arb_err_t rv;
		unsigned int i;


		/**
		 * Calculate size of outputs
		 */

		/* This is PAL-specific, so it's fine to figure it out right
		 * here. */
		counter_len = sizeof(pal_state_t);
		
		/* This is ARB-specific. Calling with NULL assigns
		 * new_snapshot_len amount of space needed. */
		rv = arb_initialize_internal_state(NULL, &new_snapshot_len);		
		if(ARB_ENONE != rv) {
			*puiRv = TZ_ERROR_SERVICE;
			/* TODO: Also assign rv somewhere! */
			break;
		}

		/* Make room for outputs */
		if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EARRSPC "%"TZI_EARRSPC,
															 &counter, (uint32_t)counter_len,
															 &new_snapshot, (uint32_t)new_snapshot_len))) {
			break;
		}

		/* Now that buffers are allocated, call for real. Note that
		 * arb_initialize_internal_state() subsequently calls the
		 * PAL-specific state initialization function(s). */
		rv = arb_initialize_internal_state(new_snapshot, &new_snapshot_len);
		
		if(ARB_ENONE != rv) {
			log_err("arb_initialize_internal_state() failed with rv %d", rv);
			*puiRv = rv;
			append_only_stderr(psOutBuf);
			break;
		}
		
		/* Now that an initial state is defined, prepare the cleartext
		 * outputs (in this case, just the counter value) */
		for(i=0; i<sizeof(pal_state_t); i++) {
			counter[i] = ((uint8_t*)&g_pal_state.counter)[i];
		}

		log_info("PAL_ARB_INITIALIZE completed successfully");
		append_stderr(psOutBuf);

		break;
	}
	/* Handle both of these here since the only real difference is wrt a
	 * boolean passed to arb_execute_request */
  case PAL_ARB_INCREMENT:
  case PAL_ARB_ATTEMPT_RECOVERY:
		/**
		 * This command tells the PAL to increment its internal counter.
		 */
	{
		size_t old_snapshot_len;
		uint8_t* old_snapshot;
		size_t counter_len;
		uint8_t* counter;
		size_t new_snapshot_len;
		uint8_t* new_snapshot;
		arb_err_t rv = ARB_ENONE;
		unsigned int i;
		pal_request_t *req;
		size_t dummy_req_len;

		if((*puiRv = TZIDecodeBufF(psInBuf,
                               "%"TZI_DARRSPC "%"TZI_DARRSPC,
                               &req, (uint32_t*)&dummy_req_len,
                               &old_snapshot, (uint32_t*)&old_snapshot_len)))
			break;

		if(dummy_req_len != sizeof(pal_request_t) ||
			 !(req->cmd == PAL_ARB_INCREMENT ||
				 req->cmd == PAL_ARB_ATTEMPT_RECOVERY)) {
			*puiRv = ARB_EBADSTATE;
			break;
		}

		/* Make room for outputs. */
		counter_len = sizeof(pal_state_t);
		/* XXX Unsafe assumption that state size never changes!!! */
		new_snapshot_len = old_snapshot_len;

		if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EARRSPC "%"TZI_EARRSPC,
															 &counter, (uint32_t)counter_len,
															 &new_snapshot, (uint32_t)new_snapshot_len))) {
			break;
		}


		rv = arb_execute_request((uiCommand == PAL_ARB_ATTEMPT_RECOVERY),
														 (const uint8_t*)req, sizeof(pal_request_t),
														 old_snapshot, old_snapshot_len,
														 new_snapshot, &new_snapshot_len);
		
		if(ARB_ENONE != rv) {
			log_err("arb_execute_request() failed with rv %d", rv);
			*puiRv = rv;
			append_only_stderr(psOutBuf);
			break;
		}

		/* Prepare the cleartext outputs (in this case, just the counter
		 * value) */
		for(i=0; i<sizeof(pal_state_t); i++) {
			counter[i] = ((uint8_t*)&g_pal_state.counter)[i];
		}

		log_info("PAL_ARB_INCREMENT completed successfully");
		append_stderr(psOutBuf);

		break;
	}
	} /* switch */
  
  return;
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* c-basic-offset: 2 */
/* End:             */
