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

#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <svcapi.h>


/* from emhf's processor.h */
static inline uint64_t rdtsc64(void)
{
  uint64_t rv;

  __asm__ __volatile__ ("rdtsc" : "=A" (rv));
  return (rv);
}

int svc_time_elapsed_us(uint64_t *epoch_nonce, /* out */
                        uint64_t *us) /* out */
{
  static uint64_t our_epoch_nonce;
  static uint32_t cycles_per_us;
  static bool initd=false;
  int rv=0;

  /* FIXME: check for constant_tsc. otherwise rdtsc is unreliable */

  /* initialize epoch nonce */
  if(!initd) {
    rv = svc_utpm_rand_block(&our_epoch_nonce, sizeof(our_epoch_nonce));
    if (rv) {
      return rv;
    }

    cycles_per_us = 2000; /* FIXME - get real cpu frequency */

    initd=true;
  }

  *epoch_nonce = our_epoch_nonce;
  /* FIXME : technically ought to serialize with, e.g. cpuid */
  *us = rdtsc64() / cycles_per_us;

  return 0;
}

int svc_utpm_seal(TPM_PCR_INFO *pcrInfo,
                  void *in,
                  size_t in_len,
                  void *out,
                  size_t *out_len)
{
  memcpy(out, pcrInfo, sizeof(*pcrInfo));
  memcpy(out+sizeof(*pcrInfo), in, in_len);
  *out_len = in_len+sizeof(*pcrInfo);
  return 0;
}

int svc_utpm_unseal(void *in,
                    size_t in_len,
                    void *out,
                    size_t *out_len,
                    void *digestAtCreation)
{
  TPM_PCR_INFO *info_at_creation = (TPM_PCR_INFO*)in;

  memcpy(digestAtCreation,
         &info_at_creation->digestAtCreation,
         sizeof(TPM_COMPOSITE_HASH));

  *out_len = in_len-sizeof(TPM_PCR_INFO);
  memcpy(out, in+sizeof(TPM_PCR_INFO), *out_len);

  return 0;
}

int svc_utpm_quote(TPM_NONCE *nonce, /* in */
                   TPM_PCR_SELECTION *tpmsel, /* in */
                   uint8_t *sig,
                   size_t *sigLen,
                   uint8_t *pcrComposite,
                   size_t *pcrCompositeLen)
{
  *sigLen=0;
  return 0;
}

int svc_utpm_pcr_extend(uint32_t idx,
                        uint8_t *meas)
{
  return 0;
}

int svc_utpm_pcr_read(uint32_t idx,
                      uint8_t* val)
{
  memset(val, 0, 20);
  return 0;
}

int svc_utpm_id_getpub(uint8_t *N,
											 size_t *out_len)
{
  return 0;
}

int svc_utpm_rand(void *out, /* out */
                  size_t *out_len) /* in,out */
{
  memset(out, 0, *out_len);
  return 0;
}

int svc_utpm_rand_block(void *out, /* out */
                        size_t out_len) /* in */
{
  memset(out, 0, out_len);
  return 0;
}

/**
 * Semantics for "fake" NVRAM: Persist what is written for the life of
 * a service invocation, but do not actually persist to disk.
 *
 * TODO: Wire it up to the logic currently residing in
 * ~hyp/trustvisor/trunk/code/app/hc_utpm.c
 */

#define FAKE_NVRAM_SIZE 32
uint8_t g_fake_nvram[FAKE_NVRAM_SIZE];

int svc_tpmnvram_getsize(size_t *size) { /* out */
  if(NULL == size) {
      return -1;
  }
  *size = FAKE_NVRAM_SIZE;

  return 0;
}

int svc_tpmnvram_readall(uint8_t *out) { /* out */
  if(NULL == out) {
      return -1;
  }

  memcpy(out, g_fake_nvram, FAKE_NVRAM_SIZE);

  return 0;
}

int svc_tpmnvram_writeall(uint8_t *in) { /* in */
  if(NULL == in) {
      return -1;
  }

  memcpy(g_fake_nvram, in, FAKE_NVRAM_SIZE);
  
  return 0;                  
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
