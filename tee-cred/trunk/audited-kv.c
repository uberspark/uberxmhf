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

#include <string.h>

#include <tee-sdk/tze.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tv.h>

#include "audited-kv.h"
#include "audited-kv-pal.h"

#include "proto-gend/db.pb-c.h"

/* set to enable userspace mode for testing */
#ifndef USERSPACE_ONLY
#define USERSPACE_ONLY 0
#endif

int akv_ctx_init(akv_ctx_t* ctx, const char* priv_key_pem)
{
  tz_return_t rv, serviceRv;
  tz_operation_t op;
  bool registered_pal=false;

  /* register pal */
  {
    tv_device_open_options_t tv_dev_options =
      (tv_device_open_options_t) {
      .userspace_only = USERSPACE_ONLY,
    };
    tze_svc_load_and_open_options_t load_options =
      (tze_svc_load_and_open_options_t) {
      .pkDeviceInit = &tv_dev_options,
    };
    struct tv_pal_sections scode_info;
    tv_service_t pal = 
      {
        .sPageInfo = &scode_info,
        .pEntry = audited_kv_pal,
      };
    tv_pal_sections_init(&scode_info,
                         PAGE_SIZE, 10*PAGE_SIZE);
    rv = TZESvcLoadAndOpen(&ctx->tz_sess,
                           &pal,
                           sizeof(pal),
                           &load_options);
    if (rv) return rv;
    registered_pal=true;
  }

  /* call init */
  rv = TZOperationPrepareInvoke(&ctx->tz_sess.tzSession,
                                AKVP_INIT,
                                NULL,
                                &op);
  if (rv) {
    goto out;
  }

  rv = TZIEncodeF(&op, "%"TZI_ESTR, priv_key_pem);
  if (rv) goto out;

  rv = TZOperationPerform(&op, &serviceRv);
  if (rv == TZ_ERROR_SERVICE)
    rv = serviceRv;

 out:
  if (rv && registered_pal) {
    TZEClose(&ctx->tz_sess);
  }

  return rv;
}

int akv_ctx_release(akv_ctx_t* ctx)
{
  tz_return_t rv;
  rv = TZEClose(&ctx->tz_sess);
  return rv;
}



tz_return_t
TZIPrepareEncodeF(tz_session_t *psSession,
                  tz_operation_t *psOp,
                  uint32_t cmd,
                  const char* str, ...)
  __attribute__ ((format (printf, 4, 5)));
tz_return_t
TZIPrepareEncodeF(tz_session_t *psSession,
                  tz_operation_t *psOp,
                  uint32_t cmd,
                  const char* str, ...)
{
  tz_return_t rv;
  va_list argp;
  va_start(argp, str);
  rv = TZOperationPrepareInvoke(psSession,
                                cmd,
                                NULL,
                                psOp);
  if (rv) goto out;
  rv = vTZIEncodeF(psOp, str, argp);
 out:
  va_end(argp);
  return rv;
}

tz_return_t
TZIExecuteDecodeF(tz_operation_t *psOp,
                  tz_return_t *serviceReturn,
                  const char* str,
                  ...)
  __attribute__ ((format (scanf, 3, 4)));
tz_return_t
TZIExecuteDecodeF(tz_operation_t *psOp,
                  tz_return_t *serviceReturn,
                  const char* str,
                  ...)
{
  tz_return_t rv;
  va_list argp;
  va_start(argp, str);

  rv = TZOperationPerform(psOp, serviceReturn);
  if (rv) goto out;
  rv = vTZIDecodeF(psOp, str, argp);
 out:
  va_end(argp);
  return rv;
}

tz_return_t start_audited_cmd_encode(tz_operation_t *psOp, uint32_t cmd)
{
  tz_return_t rv;
  rv = TZIEncodeF(psOp, "%"TZI_EU32, cmd);
  return rv;
 }

tz_return_t start_audited_cmd_decode(tz_operation_t *psOp,
                                     uint32_t *pending_cmd,
                                     void** audit_nonce, uint32_t *audit_nonce_len,
                                     void** audit_string, uint32_t *audit_string_len)
{
  tz_return_t rv;
  rv = TZIDecodeF(psOp,
                  "%"TZI_DU32 "%"TZI_DARRSPC "%"TZI_DARRSPC,
                  pending_cmd,
                  audit_nonce, audit_nonce_len,
                  audit_string, audit_string_len);
  return rv;
}

void akv_cmd_ctx_release(akv_cmd_ctx_t *ctx)
{
  TZOperationRelease(&ctx->tzStartOp);
}

int akv_db_add_begin(akv_ctx_t*  ctx,
                     akv_cmd_ctx_t* cmd_ctx,
                     const char* key,
                     const char* val)
{
  tz_return_t serviceReturn;
  int rv=0;
  Db__AddReq req = DB__ADD_REQ__INIT;
  uint32_t len;
  void *buf;

  /* FIXME- is there a way to avoid having to cast
     away the const here? */
  req.key = (char*)key;
  req.val.data = (void*)val;
  req.val.len = strlen(val);

  memset(cmd_ctx, 0, sizeof(*cmd_ctx));
  cmd_ctx->akv_ctx = ctx;

  rv = TZIPrepareEncodeF(&ctx->tz_sess.tzSession,
                         &cmd_ctx->tzStartOp,
                         AKVP_START_AUDITED_CMD,
                         "%"TZI_EU32,
                         AKVP_DB_ADD);

  len = db__add_req__get_packed_size(&req);
  buf = TZEncodeArraySpace(&cmd_ctx->tzStartOp, len);
  db__add_req__pack(&req, buf);
  /* rv = TZIEncodeF(&cmd_ctx->tzStartOp, */
  /*                 "%"TZI_ESTR "%"TZI_ESTR, */
  /*                 key, val); */

  rv = TZIExecuteDecodeF(&cmd_ctx->tzStartOp,
                         &serviceReturn,
                         "%"TZI_DU32 "%"TZI_DARRSPC "%"TZI_DARRSPC,
                         &cmd_ctx->cmd_id,
                         &cmd_ctx->audit_nonce, &cmd_ctx->audit_nonce_len,
                         &cmd_ctx->audit_string, &cmd_ctx->audit_string_len);

  if (rv != TZ_SUCCESS) {
    if (rv == TZ_ERROR_SERVICE) {
      rv = serviceReturn;
    }
  }
  return rv;
}

int akv_db_add_execute(akv_cmd_ctx_t* ctx,
                       const void* audit_token,
                       size_t audit_token_len)
{
  tz_operation_t tzOp;
  tz_return_t serviceReturn;
  int rv=0;

  rv = TZIPrepareEncodeF(&ctx->akv_ctx->tz_sess.tzSession,
                         &tzOp,
                         AKVP_EXECUTE_AUDITED_CMD,
                         "%"TZI_EU32 "%"TZI_EARR,
                         ctx->cmd_id,
                         audit_token, audit_token_len);
  rv = TZOperationPerform(&tzOp,
                          &serviceReturn);

  if (rv != TZ_SUCCESS) {
    if (rv == TZ_ERROR_SERVICE) {
      rv = serviceReturn;
    }
    goto out;
  }

 out:
  TZOperationRelease(&tzOp);
  return rv;
}
