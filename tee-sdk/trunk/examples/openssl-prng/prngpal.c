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

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include  "pal.h"

#include <tee-sdk/tzmarshal.h>
#include <tee-sdk/svcapi.h>
#include <trustvisor/tv_utpm.h> /* svc_utpm_rand_block */

#include <openssl/hmac.h>

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

  if (svc_utpm_rand_block(bytes, len) != 0) {
    *puiRv = TZ_ERROR_GENERIC;
  }

  append_stderr(psOutBuf);  

  return;
}
