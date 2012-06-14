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

#include <openssl/hmac.h>
#include <openssl/rand.h>
#include <openssl/err.h>
#include <openssl/engine.h> /* TODO: uTPM-based Engine PRNG? */

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

int test()
{
  return 5;
}

#define NUMRAND 256
static void dorand(void) {
    uint8_t bytes[NUMRAND];
    int rv;
    unsigned int i;

    rv = RAND_bytes(bytes, NUMRAND);

    fprintf(stderr, "RAND_bytes rv %d\n", rv);
    
    if(1 == rv) { /* success */
        for(i = 0; i < NUMRAND; i++) fprintf(stderr, "%02x", bytes[i]);
        fprintf(stderr, "\n");
    } else {
        fprintf(stderr, "dorand ERROR: %ld\n", ERR_get_error());
    }
}

static void dohmac(void)
    {
    HMAC_CTX ctx;
    unsigned char hmac_value[EVP_MAX_MD_SIZE];
    unsigned int hmac_len, i;
    char key[16] = "etaonrishdlcupfm";
    unsigned char buf[256];
    /* Generate digest of input stream */ 
    HMAC_Init(&ctx, key, sizeof(key), EVP_sha1());
    memcpy(buf, "abcdefghijklmnopqrstuvwxyz", 26);
    HMAC_Update(&ctx, buf, 26);
    HMAC_Final(&ctx, hmac_value, &hmac_len);
    HMAC_cleanup(&ctx);
    
    for(i = 0; i < hmac_len; i++) fprintf(stderr, "%02x", hmac_value[i]);
    fprintf(stderr, "\n");
    return;
}

void prngpal(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
  int len = 10;
  uint8_t *bytes[10];

  *puiRv = TZ_SUCCESS;
  
  fprintf(stderr, "test, %d\n", 5);
  test();
  dohmac();
  dorand();

  if (svc_utpm_rand_block(bytes, len) != 0) {
    *puiRv = TZ_ERROR_GENERIC;
  }

  append_stderr(psOutBuf);  

  return;
}
