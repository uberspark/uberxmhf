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
#include "proto-gend/akvp.pb-c.h"
#include "proto-gend/storage.pb-c.h"

/* set to enable userspace mode for testing */
#ifndef USERSPACE_ONLY
#define USERSPACE_ONLY 0
#endif

static tz_return_t akvp_invoke(akv_ctx_t* ctx,
                               uint32_t uiCommand,
                               const ProtobufCMessage *req,
                               ProtobufCMessage **res,
                               tz_return_t *svc_err)
{
  return TZEDispatchProtobuf(akvp_protos,
                             AKVP_NUM,

                             &ctx->tz_sess.tzSession,
                             uiCommand,
                             req,
                             res,
                             svc_err);
}

akv_err_t akv_ctx_init(akv_ctx_t* ctx, const char* priv_key_pem)
{
  tz_return_t tzrv;
  bool registered_pal=false;
  akv_err_t rv;

  /* register pal */
  {
    tv_device_open_options_t tv_dev_options = {
      .userspace_only = USERSPACE_ONLY,
    };
    tze_svc_load_and_open_options_t load_options = {
      .pkDeviceInit = &tv_dev_options,
    };
    struct tv_pal_sections scode_info;
    tv_service_t pal = {
      .sPageInfo = &scode_info,
      .pEntry = audited_kv_pal,
    };
    tv_pal_sections_init(&scode_info,
                         PAGE_SIZE, 10*PAGE_SIZE);
    tzrv = TZESvcLoadAndOpen(&ctx->tz_sess,
                             &pal,
                             sizeof(pal),
                             &load_options);
    if (tzrv) {
      return AKV_ETZ | (tzrv << 8);
    }
    registered_pal=true;
  }

  /* call init */
  {
    Audited__InitReq audited_init_req = {
      .base = PROTOBUF_C_MESSAGE_INIT (&audited__init_req__descriptor),
      .audit_pub_pem = (char*)priv_key_pem,
    };
    Db__InitReq db_init_req = {
      .base = PROTOBUF_C_MESSAGE_INIT (&db__init_req__descriptor),
    };
    Akvp__InitReq req = {
      .base = PROTOBUF_C_MESSAGE_INIT (&akvp__init_req__descriptor),
      .audit_init_req = &audited_init_req,
      .db_init_req = &db_init_req,
    };
    
    Akvp__InitRes *res;
    tzrv = akvp_invoke(ctx,
                       AKVP_INIT,
                       (ProtobufCMessage*)&req,
                       (ProtobufCMessage**)&res,
                       &rv);
    if (res) {
      akvp__init_res__free_unpacked(res, NULL);
    }
    if (tzrv) {
      rv = AKV_ETZ | (tzrv << 8);
      goto out;
    }
  }

 out:
  if (rv && registered_pal) {
    TZEClose(&ctx->tz_sess);
  }

  return rv;
}

akv_err_t akv_ctx_release(akv_ctx_t* ctx)
{
  tz_return_t tzrv;
  tzrv = TZEClose(&ctx->tz_sess);
  if (tzrv) {
    return AKV_ETZ | (tzrv << 8);
  } else {
    return 0;
  }
}

void akv_cmd_ctx_release(akv_cmd_ctx_t *ctx)
{
  if (ctx->audited) {
    audited__start_res__free_unpacked(ctx->audited, NULL);
    ctx->audited=NULL;
  }
}

void protobuf_c_malloc_and_pack(const ProtobufCMessage *msg,
                                void **buf,
                                size_t *len)
{
  size_t len2;
  *len = protobuf_c_message_get_packed_size(msg);
  *buf = malloc(*len);
  if(!*buf) {
    return;
  }
  len2 = protobuf_c_message_pack(msg, *buf);
  if (len2 != *len) {
    free(*buf);
    *buf=NULL;
    return;
  }
}

static akv_err_t akv_start_audited(akv_ctx_t* ctx,
                                   akv_cmd_ctx_t* cmd_ctx,
                                   uint32_t audited_cmd,
                                   const ProtobufCMessage *audited_req)
{
  akv_err_t rv=0;
  tz_return_t tzrv;
  audited_err_t audited_err;
  Audited__StartRes *start_res=NULL;
  Audited__StartReq start_req;

  start_req = (Audited__StartReq) {
    .base=PROTOBUF_C_MESSAGE_INIT (&audited__start_req__descriptor),
    .cmd=audited_cmd,
  };
  protobuf_c_malloc_and_pack(audited_req,
                             (void**)&start_req.cmd_input.data,
                             &start_req.cmd_input.len);
  if(!start_req.cmd_input.data) {
    rv = AKV_ENOMEM;
    goto out;
  }
  
  tzrv = akvp_invoke(ctx,
                     AKVP_START_AUDITED_CMD,
                     (ProtobufCMessage*)&start_req,
                     (ProtobufCMessage**)&start_res,
                     (tz_return_t*)&audited_err);
  if (tzrv) {
    rv = AKV_ETZ | (tzrv << 8);
    goto out;
  } else if (audited_err) {
    rv = AKV_EAUDITED | (audited_err << 8);
    goto out;
  }

  *cmd_ctx = (akv_cmd_ctx_t)
    { .akv_ctx = ctx,
      .audited = start_res,
    };

 out:
  free(start_req.cmd_input.data);
  start_req.cmd_input.data=NULL;
  /* Note we *don't* free start_res, since it's held in cmd_ctx */
  return rv;
}

static akv_err_t akv_execute_audited(akv_cmd_ctx_t* ctx,
                                     const void* audit_token,
                                     size_t audit_token_len,
                                     const ProtobufCMessageDescriptor* res_desc,
                                     ProtobufCMessage** res,
                                     tz_return_t *audited_fn_err)
{
  tz_return_t tzrv;
  audited_err_t audited_err;
  Audited__ExecuteRes *exec_res=NULL;
  Audited__ExecuteReq exec_req;
  akv_err_t rv=0;

  *res=NULL;

  exec_req = (Audited__ExecuteReq) {
    .base = PROTOBUF_C_MESSAGE_INIT (&audited__execute_req__descriptor),
    .pending_cmd_id = ctx->audited->res->pending_cmd_id,
    .audit_token = (ProtobufCBinaryData) {
      .data = (void*)audit_token,
      .len = audit_token_len,
    }
  };

  tzrv = akvp_invoke(ctx->akv_ctx,
                     AKVP_EXECUTE_AUDITED_CMD,
                     (ProtobufCMessage*)&exec_req,
                     (ProtobufCMessage**)&exec_res,
                     (tz_return_t*)&audited_err);

  if (audited_err) {
    rv = AKV_EAUDITED | (audited_err << 8);
    goto out;
  } else if (tzrv) {
    rv = AKV_ETZ | (tzrv << 8);
    goto out;
  }

  assert(exec_res);
  *audited_fn_err = exec_res->svc_err;
  if (exec_res->svc_err) {
    rv = exec_res->svc_err;
    goto out;
  }

  assert(exec_res->has_cmd_output);
  *res = protobuf_c_message_unpack(res_desc,
                                   NULL,
                                   exec_res->cmd_output.len,
                                   exec_res->cmd_output.data);
  if(!res) {
    rv = AKV_EPB;
    goto out;
  }

 out:
  if(exec_res) {
    protobuf_c_message_free_unpacked((ProtobufCMessage*)exec_res, NULL);
  }

  return rv;
}

akv_err_t akv_export(akv_ctx_t* ctx,
                     char **data,
                     size_t *data_len)
{
  tz_return_t tzrv;
  AkvpStorage__Everything *res=NULL;
  akv_err_t svcerr, rv=0;

  tzrv = akvp_invoke(ctx,
                     AKVP_EXPORT,
                     NULL,
                     (ProtobufCMessage**)&res,
                     (tz_return_t*)&svcerr);
  if(tzrv) {
    rv = AKV_ETZ | (tzrv << 8);
    goto out;
  }
  if(svcerr) {
    rv = svcerr;
    goto out;
  }

  printf("audit pem: %s\n", res->header->audit_pub_key_pem);

 out:
  return rv;
}


akv_err_t akv_db_add_begin(akv_ctx_t*  ctx,
                           akv_cmd_ctx_t* cmd_ctx,
                           const char* key,
                           const void* val,
                           size_t val_len)
{
  akv_err_t rv=0;
  Db__AddReq add_req;

  /* FIXME- is there a way to avoid having to cast
     away the const here? */
  add_req = (Db__AddReq) {
    .base = PROTOBUF_C_MESSAGE_INIT (&db__add_req__descriptor),
    .key = (char*)key,
    .val = (ProtobufCBinaryData) {
      .data = (void*)val,
      .len = val_len,
    }
  };

  rv = akv_start_audited(ctx,
                         cmd_ctx,
                         KV_ADD,
                         (ProtobufCMessage*)&add_req);
  return rv;
}


akv_err_t akv_db_add_execute(akv_cmd_ctx_t* ctx,
                             const void* audit_token,
                             size_t audit_token_len)
{
  akv_err_t rv=0;
  Db__AddRes *add_res=NULL;
  kv_err_t kv_err;

  rv = akv_execute_audited(ctx,
                           audit_token,
                           audit_token_len,
                           &db__add_res__descriptor,
                           (ProtobufCMessage**)&add_res,
                           (tz_return_t*)&kv_err);
  if (rv) {
    goto out;
  }
  if (kv_err) {
    rv = AKV_EKV | (kv_err << 8);
    goto out;
  }

  out:
  if(add_res) {
    db__add_res__free_unpacked(add_res, NULL);
  }

  return rv;
}

akv_err_t akv_db_get_begin(akv_ctx_t*  ctx,
                           akv_cmd_ctx_t* cmd_ctx,
                           const char* key)
{
  akv_err_t rv=0;
  Db__GetReq get_req;

  /* FIXME- is there a way to avoid having to cast
     away the const here? */
  get_req = (Db__GetReq) {
    .base = PROTOBUF_C_MESSAGE_INIT (&db__get_req__descriptor),
    .key = (char*)key,
  };

  rv = akv_start_audited(ctx,
                         cmd_ctx,
                         KV_GET,
                         (ProtobufCMessage*)&get_req);

  return rv;
}

akv_err_t akv_db_get_execute(akv_cmd_ctx_t* ctx,
                             const void* audit_token,
                             size_t audit_token_len,
                             void **val,
                             size_t *val_len)
{
  Db__GetRes *get_res=NULL;
  akv_err_t rv=0;
  kv_err_t kv_err;

  *val=NULL;

  rv = akv_execute_audited(ctx,
                           audit_token,
                           audit_token_len,
                           &db__get_res__descriptor,
                           (ProtobufCMessage**)&get_res,
                           (tz_return_t*)&kv_err);

  if (rv) {
    goto out;
  }
  if (kv_err) {
    rv = AKV_EKV | (kv_err << 8);
    goto out;
  }

  /* stealing reference from unpacked message.
     assuming default (system) allocator */
  *val_len = get_res->val.len;
  *val = get_res->val.data;
  get_res->val.data=NULL;

 out:
  if(get_res) {
    db__get_res__free_unpacked(get_res, NULL);
  }
    
  return rv;
}
