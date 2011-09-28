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

#include <malloc.h>
#include <string.h>
#include <stdio.h>
#include <sys/stat.h>

#include "tcm.h"
#include "audited-kv.h"
#include "audited-kv-pal.h"
#include "audit.h"

#include <tee-sdk/tv.h>

tcm_err_t tcm_ctx_init(tcm_ctx_t* tcm_ctx,
                       audit_ctx_t* audit_ctx,
                       akv_ctx_t* akv_ctx)
{
  if (!tcm_ctx || !audit_ctx || !akv_ctx) {
    return TCM_EINVAL;
  }
  tcm_ctx->audit_ctx = audit_ctx;
  tcm_ctx->akv_ctx = akv_ctx;

  return 0;
}

void tcm_ctx_release(tcm_ctx_t* tcm_ctx)
{
}

tcm_err_t tcm_db_add(tcm_ctx_t* tcm_ctx,
                     const char* key,
                     const char* val)
{
  akv_cmd_ctx_t akv_cmd_ctx;
  akv_err_t akv_err;
  audit_err_t audit_err;
  uint8_t audit_token[AUDIT_TOKEN_MAX];
  size_t audit_token_len = sizeof(audit_token);
  int rv = 0;

  if (!tcm_ctx || !key || !val)
    return TCM_EINVAL;

  akv_err = akv_db_add_begin(tcm_ctx->akv_ctx,
                             &akv_cmd_ctx,
                             key,
                             val,
                             strlen(val)+1);
  if (akv_err) {
    rv= TCM_EAKV;
    goto cleanup_none;
  }

  audit_err = audit_get_token(tcm_ctx->audit_ctx,
                              akv_cmd_ctx.audited->res->audit_nonce.data,
                              akv_cmd_ctx.audited->res->audit_nonce.len,
                              akv_cmd_ctx.audited->res->audit_string,
                              strlen(akv_cmd_ctx.audited->res->audit_string),
                              audit_token,
                              &audit_token_len);
  if (audit_err) {
    rv = TCM_EAUDIT;
    goto cleanup_cmd;
  }

  if (akv_db_add_execute(&akv_cmd_ctx,
                         audit_token,
                         audit_token_len)) {
    rv = TCM_EAKV;
    goto cleanup_cmd;
  }

 cleanup_cmd:
  akv_cmd_ctx_release(&akv_cmd_ctx);
 cleanup_none:
  return rv;
}

tcm_err_t tcm_db_get(tcm_ctx_t* tcm_ctx,
                     const char* key,
                     char** val)
{
  akv_cmd_ctx_t akv_cmd_ctx;
  akv_err_t akv_err;
  audit_err_t audit_err;
  uint8_t audit_token[AUDIT_TOKEN_MAX];
  size_t audit_token_len = sizeof(audit_token);
  int rv = 0;
  size_t val_len;

  if (!tcm_ctx || !key || !val)
    return TCM_EINVAL;

  akv_err = akv_db_get_begin(tcm_ctx->akv_ctx,
                             &akv_cmd_ctx,
                             key);
  if (akv_err) {
    rv= TCM_EAKV;
    goto cleanup_none;
  }

  audit_err = audit_get_token(tcm_ctx->audit_ctx,
                              akv_cmd_ctx.audited->res->audit_nonce.data,
                              akv_cmd_ctx.audited->res->audit_nonce.len,
                              akv_cmd_ctx.audited->res->audit_string,
                              strlen(akv_cmd_ctx.audited->res->audit_string),
                              audit_token,
                              &audit_token_len);
  if (audit_err) {
    rv = TCM_EAUDIT;
    goto cleanup_cmd;
  }

  if (akv_db_get_execute(&akv_cmd_ctx,
                         audit_token,
                         audit_token_len,
                         (void**)val,
                         &val_len)) {
    rv = TCM_EAKV;
    goto cleanup_cmd;
  }

 cleanup_cmd:
  akv_cmd_ctx_release(&akv_cmd_ctx);
 cleanup_none:
  return rv;
}

char* read_file(const char *path)
{
  struct stat s;
  size_t toread;
  size_t numread=0;
  FILE *f=NULL;
  char *rv=NULL;

  if (stat(path, &s)) {
    return NULL;
  }

  toread = s.st_size;

  rv = malloc(toread+1);
  if(rv == NULL) {
    return NULL;
  }

  f = fopen(path, "r");
  if(f == NULL) {
    return NULL;
  }

  while(toread > 0) {
    size_t cnt = fread(&rv[numread], 1, toread, f);
    if (cnt == 0) {
      free(rv);
      return(NULL);
    }
    toread -= cnt;
    numread += cnt;
  }
  rv[numread] = '\0';
  return rv;
}

int main(int argc, char **argv)
{
  int rv=0;
  audit_err_t audit_err;
  akv_err_t akv_err;
  tcm_err_t tcm_err;
  
  tcm_ctx_t tcm_ctx;
  audit_ctx_t audit_ctx;
  akv_ctx_t akv_ctx;
  const char* server = argv[1];
  const char* port = argv[2];
  const char* pem_pub_key_file = argv[3];
  char *pem_pub_key = read_file(pem_pub_key_file);

  audit_err = audit_ctx_init(&audit_ctx, server, port);
  if (audit_err) {
    rv = 1;
    printf("audit_ctx_init failed with rv %d\n", audit_err);
    goto cleanup_none;
  }

  akv_err = akv_ctx_init(&akv_ctx, pem_pub_key);
  if (akv_err) {
    rv = 2;
    printf("akv_ctx_init failed with rv %d\n", akv_err);
    goto cleanup_audit;
  }

  tcm_err = tcm_ctx_init(&tcm_ctx, &audit_ctx, &akv_ctx);
  if (tcm_err) {
    rv = 3;
    printf("tcm_ctx_init failed with rv %d\n", tcm_err);
    goto cleanup_akv;
  }

  tcm_err = tcm_db_add(&tcm_ctx,
                       "key",
                       "val");
  if (tcm_err) {
    rv = 4;
    printf("tcm_db_add failed with %d\n", tcm_err);
    goto cleanup_tcm;
  }

  {
    char *val;
    tcm_err = tcm_db_get(&tcm_ctx,
                         "key",
                         &val);
    if (tcm_err) {
      rv = 4;
      printf("tcm_db_add failed with %d\n", tcm_err);
      goto cleanup_tcm;
    }
    printf("retrieved val:%s\n", val);
    free(val);
    val=NULL;
  }

 cleanup_tcm:
  tcm_ctx_release(&tcm_ctx);
 cleanup_akv:
  akv_ctx_release(&akv_ctx);
 cleanup_audit:
  audit_ctx_release(&audit_ctx);
 cleanup_none:
  return rv;
} 
