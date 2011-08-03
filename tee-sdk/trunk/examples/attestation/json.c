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

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>

#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/bio.h>
#include <openssl/buffer.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>
#include <openssl/engine.h>

#include <json/json.h>

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include "json.h"

/*
 * if 'prefix' != NULL, print it before each line of hex string
 */
void print_hex(const char *prefix, const void *prtptr, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ ) {
        if ( i % 16 == 0 && prefix != NULL )
            printf("\n%s", prefix);
        printf("%02x ", *(const uint8_t *)prtptr++);
    }
    printf("\n");
}

/* Thanks: http://www.ioncannon.net/programming/34/howto-base64-encode-with-cc-and-openssl/ */
/* returns malloc'd pointer to base64-encoded string */
/* CALLEE MUST FREE IT. */
static char *base64(const unsigned char *input, int length)
{
  BIO *bmem, *b64;
  BUF_MEM *bptr;

  b64 = BIO_new(BIO_f_base64());
  bmem = BIO_new(BIO_s_mem());
  b64 = BIO_push(b64, bmem);
  BIO_write(b64, input, length);
  BIO_flush(b64);
  BIO_get_mem_ptr(b64, &bptr);

  char *buff = (char *)malloc(bptr->length);
  memcpy(buff, bptr->data, bptr->length-1);
  buff[bptr->length-1] = 0;

  BIO_free_all(b64);

  return buff;
}

int output_as_json(uint8_t *tpm_pcr_composite, uint32_t tpc_len, uint8_t *sig, uint32_t sig_len,
                   TPM_NONCE *externalnonce, uint8_t* rsaMod) {
    /* base64-encoded representations of binary variables */
    char *tpm_pcr_composite_b64 = NULL;
    char *sig_b64 = NULL;
    char *externalnonce_b64 = NULL;
    char *rsaMod_b64 = NULL;

    /* json objects to hold strings containing base64-encoded binary variables */
    json_object *jtpm_pcr_composite = NULL;
    json_object *jsig = NULL;
    json_object *jexternalnonce = NULL;
    json_object *jrsaMod = NULL;

    /* json objects to form semantic structure around the above */
    json_object *jobj = json_object_new_object(); 
    json_object *jTopLevelTitle = json_object_new_string("pal_attestation_output");
    json_object *jDataStructureVersion = json_object_new_int(1);
     
    json_object_object_add(jobj, "TopLevelTitle", jTopLevelTitle);
    json_object_object_add(jobj, "DataStructureVersion", jDataStructureVersion);    
    
    /* base64 encode useful outputs for processing with json*/
    tpm_pcr_composite_b64 = base64(tpm_pcr_composite, tpc_len);
    sig_b64 = base64(sig, sig_len);
    externalnonce_b64 = base64((uint8_t*)externalnonce, TPM_HASH_SIZE);
    rsaMod_b64 = base64(rsaMod, TPM_RSA_KEY_LEN);

    /* create json objects with base64-encoded stings */
    jtpm_pcr_composite = json_object_new_string(tpm_pcr_composite_b64);
    jsig = json_object_new_string(sig_b64);
    jexternalnonce = json_object_new_string(externalnonce_b64);
    jrsaMod = json_object_new_string(rsaMod_b64);

    json_object_object_add(jobj, "tpm_pcr_composite", jtpm_pcr_composite);
    json_object_object_add(jobj, "sig", jsig);
    json_object_object_add(jobj, "externalnonce", jexternalnonce);
    json_object_object_add(jobj, "rsaMod", jrsaMod);

    printf("The json object created: %s\n", json_object_to_json_string(jobj));
    
    /* free malloc'd stuff */    
    if(tpm_pcr_composite_b64) { free(tpm_pcr_composite_b64); tpm_pcr_composite_b64 = NULL; }
    if(sig_b64) { free(sig_b64); sig_b64 = NULL; }
    if(externalnonce_b64) { free(externalnonce_b64); externalnonce_b64 = NULL; }
    if(rsaMod_b64) { free(rsaMod_b64); rsaMod_b64 = NULL; }
    
    return 0;
}
