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
#include <string.h>
#include  "pal.h"

#include <tsvc.h> /* newlib, stderr */
#include <tee-sdk/tzmarshal.h>
#include <tee-sdk/svcapi.h>
#include <trustvisor/tv_utpm.h> /* svc_utpm_rand_block */

#include <nist_ctr_drbg.h>

#include "dbg.h"

/* DRBG parameters */
#define CTR_DRBG_SEED_BITS 256
#define CTR_DRBG_NONCE_BITS 64

char end[10*4096]; /* define the end of the data segment and some
                      buffer spacefor libnosys's sbrk */
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

static int serialize_drbg(const NIST_CTR_DRBG *drbg, uint8_t **buf, size_t *len) {
    if(!drbg || !buf || !len) { return 1; }

    *len = sizeof(NIST_CTR_DRBG);
    *buf = malloc(*len);
    if(!*buf) { return 1; }

    memcpy(*buf, drbg, *len);

    log_info("serialize_ctrdrbg SUCCESS");
    return 0;
}

static int deserialize_drbg(const uint8_t *buf, size_t len, NIST_CTR_DRBG *drbg) {
    if(!drbg || !buf || len != sizeof(NIST_CTR_DRBG)) { return 1; }

    memcpy(drbg, buf, len);

    log_info("deserialize_ctrdrbg SUCCESS");
    return 0;
}

/* returns 0 on success. */
static int initialize_ctrdrbg(NIST_CTR_DRBG *drbg) {
    uint8_t EntropyInput[CTR_DRBG_SEED_BITS/8];
    uint64_t Nonce;
    int rv = 0;

    if(!drbg) { return 1; }
    
    /* Perform deterministic initialization (e.g., expand AES key
     * schedule) */
    nist_ctr_initialize();

    /* Get CTR_DRBG_SEED_BITS of entropy from the MicroTPM */
    if (0 != (rv = svc_utpm_rand_block(EntropyInput, CTR_DRBG_SEED_BITS/8))) {
        fprintf(stderr, "ERROR %d from svc_utpm_rand_block for entropy input\n", rv);
        return rv;
    }    

    /* Also use MicroTPM to get CTR_DRBG_NONCE_BITS of initialization nonce */
    COMPILE_TIME_ASSERT(CTR_DRBG_NONCE_BITS/8 == sizeof(Nonce));
    if (0 != (rv = svc_utpm_rand_block(EntropyInput, CTR_DRBG_NONCE_BITS/8))) {
        fprintf(stderr, "ERROR %d from svc_utpm_rand_block for nonce\n", rv);
        return rv;
    }    

    if(0 != nist_ctr_drbg_instantiate(drbg, EntropyInput, sizeof(EntropyInput),
                                      &Nonce, sizeof(Nonce), NULL, 0)) {
        fprintf(stderr, "\nFATAL ERROR: nist_ctr_drbg_instantiate FAILED.\n");
        return 1;
    }				

    log_info("initialize_ctrdrbg SUCCESS");
    return rv;
}

void prngpal(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
  NIST_CTR_DRBG drbg;
  size_t len;
  uint8_t *serialized_drbg;
  uint8_t byte;
  int rv;
  unsigned int i;

  *puiRv = TZ_SUCCESS;
  
  log_info("prngpal Alive! :)");
  
  if(0 != initialize_ctrdrbg(&drbg)) {
      fprintf(stderr, "initialize_ctrdrbg FAILED!\n");
      *puiRv = TZ_ERROR_SECURITY;
      goto out;
  }  

  if(0 != serialize_drbg(&drbg, &serialized_drbg, &len)) {
      log_err("serialize_drbg FAILED!!!");
      *puiRv = TZ_ERROR_SECURITY;
      goto out;
  }

  log_hex("serialized drbg state: ", serialized_drbg, len);

  if(0 != deserialize_drbg(serialized_drbg, len, &drbg)) {
      log_err("deserialize_drbg FAILED!!!");
      *puiRv = TZ_ERROR_SECURITY;
      goto out;
  }

  for(i=0; i<10; i++) {
      if((rv = nist_ctr_drbg_generate(&drbg, &byte, sizeof(byte), NULL, 0))) {
          log_err("FATAL: nist_ctr_drbg_generate() returned error %d!\n", rv);
          *puiRv = TZ_ERROR_SECURITY;
          goto out;
      }
      
      log_info("Got a random byte! %02x", byte);
  }
  free(serialized_drbg); serialized_drbg = NULL;  
      
  out:
  nist_ctr_drbg_destroy(&drbg);
  append_stderr(psOutBuf);  

  return;
}
