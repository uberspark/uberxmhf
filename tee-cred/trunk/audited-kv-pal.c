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

#include "audited.h"
#include "audited-kv-pal.h"
#include "audited-kv-pal-fns.h"
#include "kv.h"
#include "proto-gend/db.pb-c.h"

#define FREE_AND_NULL(x) do { free(x) ; x=NULL; } while(0)
static bool did_init = false;

static int remap_err(int in, int default_val, ...)
{
  va_list ap;
  int from, to;
  
  /* 0 always maps to 0 */
  if(in == 0) return 0;

  va_start(ap, default_val);
  while(1) {
    /* keep going until we get to '0' sentinel */
    from = va_arg(ap, int);
    if(!from) break;
    to = va_arg(ap, int);
    if(!to) break;

    /* match: remap to 'to' */
    if (from==in) {
      va_end(ap);
      return to;
    }
  }
  va_end(ap);

  /* no match: return default */
  return default_val;
}

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
} akv_ctx;

akv_err_t akvp_init(const char* audit_pub_pem)
{
  audited_err_t audited_err;
  akv_err_t rv;

  if(akv_ctx.kv_ctx) {
    kv_ctx_del(akv_ctx.kv_ctx);
  }
  akv_ctx.kv_ctx = kv_ctx_new();

  audited_err = audited_init(audit_pub_pem);
  rv = remap_err(audited_err, AKV_EAUDITED,
                 AUDITED_EBADKEY, AKV_EBADKEY,
                 0,0);

  if(!rv) {
    did_init = true;
  }

  return rv;
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

void akvp_db_add_release_req(void* vreq)
{
  db__add_req__free_unpacked(vreq, NULL);
}

int akvp_db_add_begin_decode_req(void **vcont,
                                 void *inbuf,
                                 size_t inbuf_len)
{
  Db__AddReq *req=NULL;
  void *inbuf_proto;
  uint32_t inbuf_proto_len;
  inbuf_proto = TZIDecodeArraySpace(inbuf, &inbuf_proto_len);

  req = db__add_req__unpack(NULL, inbuf_proto_len, inbuf_proto);
  *vcont=req;
  if(req)
    return 0;
  else
    return AKV_EDECODE;
}

int akvp_db_add_audit_string(void *vreq,
                             char **audit_string)
{
  Db__AddReq *req = (Db__AddReq*)vreq;
  *audit_string = /* FIXME need to escape nulls and non-printables,
                     and make sure null-terminated.
                  */
    sprintf_mallocd("ADD{key=\"%s\"}", req->key);

  return AKV_ENONE;
}

int akvp_db_add_execute(void* vreq, void **vres)
{
  Db__AddReq *req = (Db__AddReq*)vreq;
  akv_err_t akv_err;
  kv_err_t kv_err;

  *vres = NULL;

  kv_err = kv_add(akv_ctx.kv_ctx, req->key, strlen(req->key), req->val.data, req->val.len);
  akv_err =
    (kv_err == KV_ENONE) ? AKV_ENONE
    : (kv_err == KV_EEXISTS) ? AKV_EEXISTS
    : AKV_EKV;

  return akv_err;
}

size_t akvp_db_add_encode_res_len(void* vres)
{
  return 0;
}

void akvp_db_add_release_res(void* vres)
{
}

int akvp_db_add_encode_res(void *vres, void* buf)
{
  return 0;
}

typedef struct {
  void *key;
  size_t key_len;
} akvp_db_get_cont_t;

int akvp_db_get_begin_marshal(char **audit_string,
                              void **vcont,
                              struct tzi_encode_buffer_t *psInBuf)
{
  void *key;
  uint32_t key_len;

  key = TZIDecodeArraySpace(psInBuf, &key_len);

  if (TZIDecodeGetError(psInBuf)) {
    return AKV_EDECODE;
  }

  return akvp_db_get_begin(audit_string, vcont, key, key_len);
}

akv_err_t akvp_db_get_begin(char **audit_string,
                            void **vcont,
                            const void* key, size_t key_len)
{
  akvp_db_get_cont_t **pp_cont = ((akvp_db_get_cont_t**)vcont);
  akvp_db_get_cont_t *cont;

  *pp_cont = malloc(sizeof(**pp_cont));
  if(!pp_cont) {
    return AKV_ENOMEM;
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
    return AKV_ENOMEM;
  }

  memcpy(cont->key, key, key_len);

  return AKV_ENONE;
}

int akvp_db_get_execute(void* vcont, struct tzi_encode_buffer_t *psOutBuf)
{
  kv_err_t kv_err;
  akvp_db_get_cont_t *cont = (akvp_db_get_cont_t*)vcont;
  const void *val;
  size_t val_len;
  akv_err_t akv_err;

  kv_err = kv_get(akv_ctx.kv_ctx, cont->key, cont->key_len, &val, &val_len);
  akv_err =
    (kv_err == KV_ENONE) ? AKV_ENONE
    : (kv_err == KV_ENOTFOUND) ? AKV_ENOTFOUND
    : AKV_EKV;

  if (akv_err) {
    return akv_err;
  }

  TZIEncodeArray(psOutBuf, val, val_len);
  if(TZIDecodeGetError(psOutBuf)) {
    return AKV_EENCODE;
  }
  return akv_err;
}

void akvp_db_get_release(void* vcont)
{
  akvp_db_get_cont_t *cont = (akvp_db_get_cont_t*)vcont;
  FREE_AND_NULL(cont->key);
  free(cont);
}

