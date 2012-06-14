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

/* 
 * Author - Jim Newsome (jnewsome@no-fuss.com)
 */

#include <stdbool.h>

/* TV */
#include <tee-sdk/tv.h>

/* local */
#include "sealed-code-pal-priv.h"

static struct {
  uint8_t unsealed[SCP_MAX_UNSEALED_LEN]; /* XXX overloading this macro. XXX need to set up storage for this and make it executable */
} pal_static __attribute__ ((section(".sdata"))) = {{0}};

__attribute__ ((section (".scode")))
static int do_seal(uint8_t *unsealed, size_t unsealed_len,
                   uint8_t *sealed, size_t *sealed_len)
{
  TPM_PCR_INFO pcrInfo;
  unsigned int i;

  /*memset(&pcrInfo, 0, sizeof(pcrInfo));*/ /* no memset in here */

  pcrInfo.pcrSelection.sizeOfSelect = 0; /* no PCRs */
  
  return svc_utpm_seal(&pcrInfo, 
                       unsealed, unsealed_len,
                       sealed, sealed_len);
}

__attribute__ ((section (".scode")))
static int do_load(uint8_t *code, size_t code_len,
                   uint8_t *params, size_t params_len,
                   uint8_t *output, size_t *output_len)
{
  size_t unsealed_len = sizeof(pal_static.unsealed);
  scp_sealed_fn_t fn = (scp_sealed_fn_t)pal_static.unsealed;
  int rv;
  uint8_t digestAtCreation[20];
  
  if((rv = svc_utpm_unseal(code, code_len,
                           pal_static.unsealed, &unsealed_len,
                           digestAtCreation))) {
    return rv;
  }

  /* TODO Check source of sealed data */
  /* TODO extend PCR with loaded code */

  fn(params, params_len, output, output_len);

/* change this to 1 modify the PAL to export the unsealed data */
#if 0
  {
    int i;
    for(i=0; i<unsealed_len; i++) {
       output[i] = pal_static.unsealed[i];
    }
    *output_len = unsealed_len;
  }
#endif

  return 0;
}

__attribute__ ((section (".scode")))
void sealed_code_pal(struct scp_in_msg *in, size_t in_len,
                     struct scp_out_msg *out, size_t *out_len)
{
  if (in_len < sizeof(*in)) {
    out->status = -1;
    return;
  }
  if (*out_len < sizeof(*out)) {
    out->status = -2;
    return;
  }
  if ((uintptr_t)in == (uintptr_t)out) {
    /* XXX really ought to check more comprehensively for overlap */
    out->status = -3;
    return;
  }
  
  switch(in->command) {
  case SCP_SEAL:
    out->status = do_seal(in->m.seal.code, in->m.seal.code_len,
                          out->r.seal.code, &out->r.seal.code_len);
    break;
  case SCP_LOAD:
    out->r.load.output_len = sizeof(out->r.load.output);
    out->status = do_load(in->m.load.code, in->m.load.code_len,
                          in->m.load.params, in->m.load.params_len,
                          out->r.load.output, &out->r.load.output_len);
    break;
  default:
    out->status = -4;
  }
}
