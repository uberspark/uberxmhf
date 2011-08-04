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
#include <string.h>
#include <malloc.h>
#include <assert.h>
#include <stdarg.h>

#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include <openssl/bio.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/engine.h>

#include "audited-kv-pal.h"
#include "audited-kv-pal-fns.h"
#include "kv.h"


#define FREE_AND_NULL(x) do { free(x) ; x=NULL; } while(0)

/* static char* strcpy_mallocd(const char *src) */
/* { */
/*   size_t len = strlen(src)+1; */
/*   char *rv = malloc(len); */
/*   if(!rv) { */
/*     return NULL; */
/*   } */
/*   strcpy(rv, src); */
/*   return rv; */
/* } */
static struct {
  kv_ctx_t* kv_ctx;
  RSA* audit_pub_key;
} akv_ctx;

void akvp_init(const char* audit_server_pub_pem)
{
  BIO *mem;

  if(akv_ctx.kv_ctx) {
    kv_ctx_del(akv_ctx.kv_ctx);
  }
  akv_ctx.kv_ctx = kv_ctx_new();
  
  mem = BIO_new_mem_buf((char*)audit_server_pub_pem, -1);
  akv_ctx.audit_pub_key =
    PEM_read_bio_RSA_PUBKEY(mem, NULL, NULL, NULL);
}

void akvp_release(void)
{
  kv_ctx_del(akv_ctx.kv_ctx);
  akv_ctx.kv_ctx=NULL;
}

char* sprintf_mallocd(const char *format, ...)
{
  va_list argp1;
  va_list argp2;
  size_t sz, sz2;
  char *rv=NULL;

  va_start(argp1, format);
  va_copy(argp2, argp1);

  sz = 1+vsnprintf(NULL, 0, format, argp1);
  rv = malloc(sz);
  if (!rv)
    goto out;
  sz2 = vsnprintf(rv, sz, format, argp2);
  assert(sz2 == (sz-1));

 out:
  va_end(argp1);
  va_end(argp2);
  return rv;
}

typedef struct {
  void *key;
  size_t key_len;
  void *val;
  size_t val_len;
} akvp_db_add_cont_t;

void akvp_db_add_release(void* vcont)
{
  akvp_db_add_cont_t *cont = (akvp_db_add_cont_t*)vcont;
  FREE_AND_NULL(cont->key);
  FREE_AND_NULL(cont->val);
  free(cont);
}

tz_return_t akvp_db_add_begin_marshal(char **audit_string,
                                      void **vcont,
                                      struct tzi_encode_buffer_t *psInBuf)
{
  char *key, *val;
  uint32_t key_len, val_len;

  key = TZIDecodeArraySpace(psInBuf, &key_len);
  val = TZIDecodeArraySpace(psInBuf, &val_len);

  if (TZIDecodeGetError(psInBuf)) {
    return TZIDecodeGetError(psInBuf);
  }

  return akvp_db_add_begin(audit_string, vcont, key, key_len, val, val_len);
}


tz_return_t akvp_db_add_begin(char **audit_string,
                              void **vcont,
                              const void* key, size_t key_len,
                              const void* val, size_t val_len)
{
  akvp_db_add_cont_t **pp_cont = ((akvp_db_add_cont_t**)vcont);
  akvp_db_add_cont_t *cont;

  *pp_cont = malloc(sizeof(**pp_cont));
  if(!pp_cont) {
    return TZ_ERROR_MEMORY;
  }
  cont = *pp_cont;

  *cont = (akvp_db_add_cont_t) {
    .key = malloc(key_len),
    .key_len = key_len,
    .val = malloc(val_len),
    .val_len = val_len,
  };
  *audit_string = /* FIXME need to escape nulls and non-printables,
                     and make sure null-terminated.
                  */
    sprintf_mallocd("ADD{key=\"%s\"}", (char*)key);

  if (!cont->key
      || !cont->val
      || !*audit_string) {
    FREE_AND_NULL(cont->key);
    FREE_AND_NULL(cont->val);
    FREE_AND_NULL(cont);
    FREE_AND_NULL(*audit_string);
    return TZ_ERROR_MEMORY;
  }

  memcpy(cont->key, key, key_len);
  memcpy(cont->val, val, val_len);

  return TZ_SUCCESS;
}

tz_return_t akvp_db_add_execute(void* vcont, struct tzi_encode_buffer_t *psOutBuf)
{
  akvp_db_add_cont_t *cont = (akvp_db_add_cont_t*)vcont;
  tz_return_t rv;
  int kv_rv;

  kv_rv = kv_add(akv_ctx.kv_ctx, cont->key, cont->key_len, cont->val, cont->val_len);
  rv =
    (kv_rv == KV_ENONE) ? AKV_ENONE
    : (kv_rv == KV_EEXISTS) ? AKV_EEXISTS
    : AKV_EKV;

  return rv;
}

typedef struct {
  void *key;
  size_t key_len;
} akvp_db_get_cont_t;

tz_return_t akvp_db_get_begin_marshal(char **audit_string,
                                      void **vcont,
                                      struct tzi_encode_buffer_t *psInBuf)
{
  void *key;
  uint32_t key_len;

  key = TZIDecodeArraySpace(psInBuf, &key_len);

  if (TZIDecodeGetError(psInBuf)) {
    return TZIDecodeGetError(psInBuf);
  }

  return akvp_db_get_begin(audit_string, vcont, key, key_len);
}

tz_return_t akvp_db_get_begin(char **audit_string,
                              void **vcont,
                              const void* key, size_t key_len)
{
  akvp_db_get_cont_t **pp_cont = ((akvp_db_get_cont_t**)vcont);
  akvp_db_get_cont_t *cont;

  *pp_cont = malloc(sizeof(**pp_cont));
  if(!pp_cont) {
    return TZ_ERROR_MEMORY;
  }
  cont = *pp_cont;

  *cont = (akvp_db_get_cont_t) {
    .key = malloc(key_len),
    .key_len = key_len,
  };
  *audit_string = /* FIXME need to escape nulls and non-printables,
                     and make sure null-terminated.
                  */
    sprintf_mallocd("GET{key=\"%s\"}", (char*)key);

  if (!cont->key
      || !*audit_string) {
    FREE_AND_NULL(cont->key);
    FREE_AND_NULL(cont);
    FREE_AND_NULL(*audit_string);
    return TZ_ERROR_MEMORY;
  }

  memcpy(cont->key, key, key_len);

  return TZ_SUCCESS;
}

tz_return_t akvp_db_get_execute(void* vcont, struct tzi_encode_buffer_t *psOutBuf)
{
  int kv_rv;
  akvp_db_get_cont_t *cont = (akvp_db_get_cont_t*)vcont;
  const void *val;
  size_t val_len;
  tz_return_t rv;

  kv_rv = kv_get(akv_ctx.kv_ctx, cont->key, cont->key_len, &val, &val_len);
  rv =
    (kv_rv == KV_ENONE) ? TZ_SUCCESS
    : (kv_rv == KV_ENOTFOUND) ? AKV_ENOTFOUND
    : AKV_EKV;

  if (rv != TZ_SUCCESS) {
    return rv;
  }

  TZIEncodeArray(psOutBuf, val, val_len);
  if(TZIDecodeGetError(psOutBuf)) {
    return TZIDecodeGetError(psOutBuf);
  }
  return rv;
}

void akvp_db_get_release(void* vcont)
{
  akvp_db_get_cont_t *cont = (akvp_db_get_cont_t*)vcont;
  FREE_AND_NULL(cont->key);
  free(cont);
}
