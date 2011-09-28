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

#include "kv.h"
#include "audited.h"
#include "audited-stubs.h"
#include "audited-kv.h"
#include "audited-kv-pal.h"

#include "proto-gend/db.pb-c.h"
#include "proto-gend/audited.pb-c.h"

/* set to enable userspace mode for testing */
#ifndef USERSPACE_ONLY
#define USERSPACE_ONLY 0
#endif

int akv_ctx_init(akv_ctx_t* ctx, const char* priv_key_pem)
{
  tz_return_t rv;
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
  {
    Audited__InitReq req = {
      .base = PROTOBUF_C_MESSAGE_INIT (&audited__init_req__descriptor),
      .audit_pub_pem = (char*)priv_key_pem,
    };
    Audited__InitRes *res;
    tze_pb_err_t pb_err;
    pb_err = audited_invoke(&ctx->tz_sess.tzSession,
                            AKVP_INIT,
                            (ProtobufCMessage*)&req,
                            (ProtobufCMessage**)&res,
                            &rv);
    if (res) {
      audited__init_res__free_unpacked(res, NULL);
    }
    if (pb_err) {
      rv = AUDITED_EPB_ERR | (pb_err << 8);
      goto out;
    }
  }

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

/* tz_return_t */
/* TZIPrepareEncodeF(tz_session_t *psSession, */
/*                   tz_operation_t *psOp, */
/*                   uint32_t cmd, */
/*                   const char* str, ...) */
/*   __attribute__ ((format (printf, 4, 5))); */
/* tz_return_t */
/* TZIPrepareEncodeF(tz_session_t *psSession, */
/*                   tz_operation_t *psOp, */
/*                   uint32_t cmd, */
/*                   const char* str, ...) */
/* { */
/*   tz_return_t rv; */
/*   va_list argp; */
/*   va_start(argp, str); */
/*   rv = TZOperationPrepareInvoke(psSession, */
/*                                 cmd, */
/*                                 NULL, */
/*                                 psOp); */
/*   if (rv) goto out; */
/*   rv = vTZIEncodeF(psOp, str, argp); */
/*  out: */
/*   va_end(argp); */
/*   return rv; */
/* } */

/* tz_return_t */
/* TZIExecuteDecodeF(tz_operation_t *psOp, */
/*                   tz_return_t *serviceReturn, */
/*                   const char* str, */
/*                   ...) */
/*   __attribute__ ((format (scanf, 3, 4))); */
/* tz_return_t */
/* TZIExecuteDecodeF(tz_operation_t *psOp, */
/*                   tz_return_t *serviceReturn, */
/*                   const char* str, */
/*                   ...) */
/* { */
/*   tz_return_t rv; */
/*   va_list argp; */
/*   va_start(argp, str); */

/*   rv = TZOperationPerform(psOp, serviceReturn); */
/*   if (rv) goto out; */
/*   rv = vTZIDecodeF(psOp, str, argp); */
/*  out: */
/*   va_end(argp); */
/*   return rv; */
/* } */

void akv_cmd_ctx_release(akv_cmd_ctx_t *ctx)
{
  if (ctx->audited) {
    audited__start_res__free_unpacked(ctx->audited, NULL);
    ctx->audited=NULL;
  }
}

akv_err_t akv_db_add_begin(akv_ctx_t*  ctx,
                           akv_cmd_ctx_t* cmd_ctx,
                           const char* key,
                           const char* val)
{
  akv_err_t rv=0;
  Db__AddReq add_req;
  Audited__StartRes *start_res=NULL;
  tze_pb_err_t tze_pb_err;
  audited_err_t audited_err;

  /* FIXME- is there a way to avoid having to cast
     away the const here? */
  add_req = (Db__AddReq) {
    .base = PROTOBUF_C_MESSAGE_INIT (&db__add_req__descriptor),
    .key = (char*)key,
    .val = (ProtobufCBinaryData) {
      .data = (void*)val,
      .len = strlen(val),
    }
  };

  tze_pb_err = audited_invoke_start(&ctx->tz_sess.tzSession,
                                    KV_ADD,
                                    (ProtobufCMessage*)&add_req,
                                    &start_res,
                                    &audited_err);
  if (audited_err) {
    rv = AKV_EAUDITED | (audited_err << 8);
    goto out;
  } else if (tze_pb_err) {
    rv = AKV_EPB | (tze_pb_err << 8);
    goto out;
  }

  *cmd_ctx = (akv_cmd_ctx_t)
    { .akv_ctx = ctx,
      .audited = start_res,
    };

 out:
  return rv;
}

akv_err_t akv_db_add_execute(akv_cmd_ctx_t* ctx,
                             const void* audit_token,
                             size_t audit_token_len)
{
  akv_err_t rv=0;
  tze_pb_err_t tze_pb_err;
  audited_err_t audited_err;
  Audited__ExecuteRes *res=NULL;
  Audited__ExecuteReq req = (Audited__ExecuteReq) {
    .base = PROTOBUF_C_MESSAGE_INIT (&audited__execute_req__descriptor),
    .pending_cmd_id = ctx->audited->res->pending_cmd_id,
    .audit_token = (ProtobufCBinaryData) {
      .data = (void*)audit_token,
      .len = audit_token_len,
    }
  };

  tze_pb_err = audited_invoke(&ctx->akv_ctx->tz_sess.tzSession,
                              AKVP_EXECUTE_AUDITED_CMD,
                              (ProtobufCMessage*)&req,
                              (ProtobufCMessage**)&res,
                              &audited_err);
  if (audited_err) {
    rv = AKV_EAUDITED | (audited_err << 8);
    goto out;
  } else if (tze_pb_err) {
    rv = AKV_EPB | (tze_pb_err << 8);
    goto out;
  }

  if(res) {
    audited__execute_res__free_unpacked(res, NULL);
    res=NULL;
  }
 out:
  return rv;
}
