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

/**
 * AntiRollBack (ARB) Tools - Trusted portion.
 *
 * These library calls are used within a PAL to achieve crash
 * resilience and anti-rollback of PAL state.
 */

#ifndef _LIBARB_H_
#define _LIBARB_H_

#include "sha1.h"

/* Starting point poached from audited-kv-errs.h. TODO: Centralize
 * some kinds of error codes, especially those TZ-related. */
typedef enum {
  ARB_ENONE=0,	
  ARB_EEXISTS=1,
  ARB_ENOTFOUND=2,
  ARB_EKV=3,
  ARB_EBADAUDITEDCMD=4,
  ARB_EBADCMDHANDLE=5,
  ARB_EBADSTATE=6,
  ARB_EDECODE=7, /* TZ Decoder returned an error */
  ARB_EENCODE=8, /* TZ Encoder returned an error */
  ARB_EPARAM=9, /* illegal params */
  ARB_EBADKEY=10,
  ARB_EBADCMD=11,
  ARB_ENOMEM=12,
  ARB_EAUDITED=13,
  ARB_EPB=14,
  ARB_EBADAUTH=15,
  ARB_ETZ=16, /* TZ error shifted on */
  ARB_EWEDGED=17, /* Unrecoverable state error! */
	ARB_EUNSEALFAILED=18,
	ARB_ERECOVERYNEEDED=19,
} arb_err_t;

#define ARB_SYM_KEY_SIZE (256/8) /* bytes */
#define ARB_HIST_SUM_LEN SHA_DIGEST_LENGTH
typedef struct {
    uint32_t dummy_prng_state; /* FIXME: implement an actual PRNG */
    /* uint8_t symmetric_key[ARB_SYM_KEY_SIZE]; */
    uint8_t history_summary[ARB_HIST_SUM_LEN]; /* TODO: Algorithm agility */
} arb_internal_state_t;



arb_err_t arb_initialize_internal_state();
arb_err_t arb_execute_request(bool attempt_recovery,
															const uint8_t *request,
                              const size_t request_len,
                              /*const*/ uint8_t *old_snapshot,
                              size_t old_snapshot_len,
															uint8_t *new_snapshot,
															size_t *new_snapshot_len);


/**
 * PALs that wish to be amenable to AntiRollBack protections MUST
 * implement these 4 functions.
 */
arb_err_t pal_arb_serialize_state(OUT uint8_t *serialized_state,
                                  OUT size_t *serialized_state_len);

arb_err_t pal_arb_deserialize_state(IN const uint8_t *serialized_state,
                                    IN const size_t serialized_state_len);

arb_err_t pal_arb_initialize_state(void);

arb_err_t pal_arb_advance_state(IN const uint8_t *request,
                                IN size_t request_len);



#endif /* _LIBARB_H_ */


/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
