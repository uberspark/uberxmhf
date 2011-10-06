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

#include "audited-kv-pal-int.h"
#include "audited.h"
#include "audited-kv-pal.h"
#include "audited-kv-pal-fns.h"
#include "kv.h"
#include "proto-gend/db.pb-c.h"
#include "proto-gend/audited.pb-c.h"

#define FREE_AND_NULL(x) do { free(x) ; x=NULL; } while(0)
static bool did_init = false;

/* static int remap_err(int in, int default_val, ...) */
/* { */
/*   va_list ap; */
/*   int from, to; */
  
/*   /\* 0 always maps to 0 *\/ */
/*   if(in == 0) return 0; */

/*   va_start(ap, default_val); */
/*   while(1) { */
/*     /\* keep going until we get to '0' sentinel *\/ */
/*     from = va_arg(ap, int); */
/*     if(!from) break; */
/*     to = va_arg(ap, int); */
/*     if(!to) break; */

/*     /\* match: remap to 'to' *\/ */
/*     if (from==in) { */
/*       va_end(ap); */
/*       return to; */
/*     } */
/*   } */
/*   va_end(ap); */

/*   /\* no match: return default *\/ */
/*   return default_val; */
/* } */

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

akv_ctx_t akv_ctx;

akv_err_t akvp_init(const Akvp__InitReq *req, Akvp__InitRes *res)
{
  audited_err_t audited_err;
  akv_err_t rv=0;
  int svcapirv;

  if(akv_ctx.kv_ctx) {
    kv_ctx_del(akv_ctx.kv_ctx);
  }
  akv_ctx.kv_ctx = kv_ctx_new();

  audited_err = audited_init(req->audit_init_req->audit_pub_pem);
  if (audited_err) {
    rv = AKV_EAUDITED | (audited_err << 8);
    goto out;
  }

  if(akv_ctx.master_secret) {
    free(akv_ctx.master_secret);
    akv_ctx.master_secret=NULL;
  }
  akv_ctx.master_secret_len = AKVP_MASTER_SECRET_LEN;
  akv_ctx.master_secret = malloc(akv_ctx.master_secret_len);
  if(!akv_ctx.master_secret) {
    rv = AKV_ENOMEM;
    goto out;
  }
  svcapirv = svc_utpm_rand_block(akv_ctx.master_secret,
                                 akv_ctx.master_secret_len);
  if (svcapirv) {
    rv = AKV_ESVC | (svcapirv << 8);
    goto out;
  }

  if(!rv) {
    did_init = true;
  }

 out:
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

akv_err_t akvp_db_add_audit_string(Db__AddReq *req,
                             char **audit_string)
{
  *audit_string = /* FIXME need to escape nulls and non-printables,
                     and make sure null-terminated.
                  */
    sprintf_mallocd("ADD{key=\"%s\"}", req->key);

  return AKV_ENONE;
}

akv_err_t akvp_db_add_execute(const Db__AddReq* req, const Db__AddRes *res)
{
  akv_err_t akv_err;
  kv_err_t kv_err;

  kv_err = kv_add(akv_ctx.kv_ctx, req->key, strlen(req->key), req->val.data, req->val.len);
  akv_err =
    (kv_err == KV_ENONE) ? AKV_ENONE
    : (kv_err == KV_EEXISTS) ? AKV_EEXISTS
    : AKV_EKV;

  return akv_err;
}

akv_err_t akvp_db_get_audit_string(Db__GetReq *req,
                             char **audit_string)
{
  *audit_string = /* FIXME need to escape nulls and non-printables,
                     and make sure null-terminated.
                  */
    sprintf_mallocd("GET{key=\"%s\"}", req->key);

  return AKV_ENONE;
}

akv_err_t akvp_db_get_execute(const Db__GetReq* req, Db__GetRes *res)
{
  akv_err_t akv_err;
  kv_err_t kv_err;

  kv_err = kv_get(akv_ctx.kv_ctx,
                  req->key,
                  strlen(req->key),
                  (const void **)(&res->val.data),
                  &res->val.len);
  akv_err =
    (kv_err == KV_ENONE) ? AKV_ENONE
    : (kv_err == KV_ENOTFOUND) ? AKV_ENOTFOUND
    : AKV_EKV;

  return akv_err;
}
