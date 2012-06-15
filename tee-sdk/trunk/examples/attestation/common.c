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
            fprintf(stderr, "\n%s", prefix);
        fprintf(stderr, "%02x ", *(const uint8_t *)prtptr++);
    }
    fprintf(stderr, "\n");
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
                   TPM_NONCE *externalnonce, uint8_t* rsaPub, uint32_t rsaPubLen) {
    /* base64-encoded representations of binary variables */
    char *tpm_pcr_composite_b64 = NULL;
    char *sig_b64 = NULL;
    char *externalnonce_b64 = NULL;
    char *rsaPub_b64 = NULL;

    /* json objects to hold strings containing base64-encoded binary variables */
    json_object *jtpm_pcr_composite = NULL;
    json_object *jsig = NULL;
    json_object *jexternalnonce = NULL;
    json_object *jrsaPub = NULL;

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
    rsaPub_b64 = base64(rsaPub, rsaPubLen);

    /* create json objects with base64-encoded stings */
    jtpm_pcr_composite = json_object_new_string(tpm_pcr_composite_b64);
    jsig = json_object_new_string(sig_b64);
    jexternalnonce = json_object_new_string(externalnonce_b64);
    jrsaPub = json_object_new_string(rsaPub_b64);

    json_object_object_add(jobj, "tpm_pcr_composite", jtpm_pcr_composite);
    json_object_object_add(jobj, "sig", jsig);
    json_object_object_add(jobj, "externalnonce", jexternalnonce);
    json_object_object_add(jobj, "rsaPub", jrsaPub);

    fprintf(stderr, "The json object created: \n");
    printf("%s\n", json_object_to_json_string(jobj));
    
    /* free malloc'd stuff (I'm told free copes fine with a NULL pointer) */    
    free(tpm_pcr_composite_b64); tpm_pcr_composite_b64 = NULL;
    free(sig_b64); sig_b64 = NULL;
    free(externalnonce_b64); externalnonce_b64 = NULL;
    free(rsaPub_b64); rsaPub_b64 = NULL;

    /* free json stuff */
    json_object_put(jobj); /* recursively frees other objects */
    
    return 0;
}

int verify_quote(uint8_t *tpm_pcr_composite, uint32_t tpc_len, uint8_t *sig, uint32_t sig_len,
                 TPM_NONCE *externalnonce, uint8_t* rsaPub, uint32_t rsaPubLen) {
    TPM_QUOTE_INFO quote_info;
    RSA *rsa = NULL;
    int rv=0;
    
    /* 1) 1.1.0.0 for consistency w/ TPM 1.2 spec */
    *((uint32_t*)&quote_info.version) = 0x00000101; 
    /* 2) 'QUOT' */
    *((uint32_t*)quote_info.fixed) = 0x544f5551; 

    /* 3) SHA-1 hash of TPM_PCR_COMPOSITE */
    SHA1(tpm_pcr_composite, tpc_len, quote_info.digestValue.value);

    print_hex("  COMPOSITE_HASH: ", quote_info.digestValue.value, TPM_HASH_SIZE);
    
    /* 4) external nonce */
    memcpy(quote_info.externalData.nonce, externalnonce->nonce, TPM_HASH_SIZE);

    //print_hex("  quote_info: ", (uint8_t*)&quote_info, sizeof(TPM_QUOTE_INFO));
    
    /**
     * Assemble the public key used to check the quote.
     */    
    if (NULL == d2i_RSAPublicKey( &rsa, (const unsigned char**)&rsaPub, rsaPubLen)) {
      fprintf(stderr, "ERROR: d2i_RSAPublicKey() failed\n");
      rv = 1;
      goto out;
    }

    /**
     * Verify the signature!
     */
    
    uint8_t valData[TPM_HASH_SIZE];
    SHA1((uint8_t*)&quote_info, sizeof(TPM_QUOTE_INFO), valData);
    //print_hex("  valData: ", valData, TPM_HASH_SIZE);

    if(1 != RSA_verify(NID_sha1, valData, TPM_HASH_SIZE, sig, sig_len, rsa)) {
        fprintf(stderr, "ERROR: Quote verification FAILED!\n");
        ERR_print_errors_fp(stdout);
        rv = 1;
        goto out;
    } else {
        fprintf(stderr, "  RSA_verify: SUCCESSfully verified quote\n");
        rv = 0;
    }
    
  out:
    /* RSA_free() frees the RSA structure and its components. The key
     * is erased before the memory is returned to the system. */
    if(rsa) { RSA_free(rsa); rsa = NULL; }
    
    return 0;
}
