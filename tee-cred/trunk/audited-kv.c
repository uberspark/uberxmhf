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

void akv_cmd_ctx_release(akv_cmd_ctx_t *ctx)
{
  if (ctx->audited) {
    audited__start_res__free_unpacked(ctx->audited, NULL);
    ctx->audited=NULL;
  }
}

static akv_err_t akv_invoke_start(akv_ctx_t* ctx,
                                  akv_cmd_ctx_t* cmd_ctx,
                                  uint32_t audited_cmd,
                                  const ProtobufCMessage *audited_req)
{
  akv_err_t rv=0;
  tze_pb_err_t tze_pb_err;
  audited_err_t audited_err;
  Audited__StartRes *start_res=NULL;
  
  tze_pb_err = audited_invoke_start(&ctx->tz_sess.tzSession,
                                    audited_cmd,
                                    audited_req,
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

static akv_err_t akv_execute(akv_cmd_ctx_t* ctx,
                             const void* audit_token,
                             size_t audit_token_len,
                             const ProtobufCMessageDescriptor* desc,
                             ProtobufCMessage** res)
{
  tze_pb_err_t tze_pb_err;
  audited_err_t audited_err;
  Audited__ExecuteRes *exec_res=NULL;
  akv_err_t rv=0;

  *res=NULL;

  tze_pb_err = audited_invoke_execute(&ctx->akv_ctx->tz_sess.tzSession,
                                      ctx->audited->res->pending_cmd_id,
                                      audit_token,
                                      audit_token_len,
                                      &audited_err,
                                      &exec_res);

  if (audited_err) {
    rv = AKV_EAUDITED | (audited_err << 8);
    goto out;
  } else if (tze_pb_err) {
    rv = AKV_EPB | (tze_pb_err << 8);
    goto out;
  }

  assert(exec_res);
  if (exec_res->svc_err) {
    rv = exec_res->svc_err;
    goto out;
  }

  assert(exec_res->has_cmd_output);
  *res = protobuf_c_message_unpack(desc,
                                   NULL,
                                   exec_res->cmd_output.len,
                                   exec_res->cmd_output.data);
  if(!res) {
    rv = AKV_EDECODE;
    goto out;
  }

 out:
  if(exec_res) {
    protobuf_c_message_free_unpacked((ProtobufCMessage*)exec_res, NULL);
  }

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

  rv = akv_invoke_start(ctx,
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

  rv = akv_execute(ctx,
                   audit_token,
                   audit_token_len,
                   &db__add_res__descriptor,
                   (ProtobufCMessage**)&add_res);

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

  rv = akv_invoke_start(ctx,
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

  rv = akv_execute(ctx,
                   audit_token,
                   audit_token_len,
                   &db__get_res__descriptor,
                   (ProtobufCMessage**)&get_res);

  *val_len = get_res->val.len;
  *val = malloc(*val_len);
  if(!*val) {
    abort();
  }
  memcpy(*val, get_res->val.data, *val_len);

  db__get_res__free_unpacked(get_res, NULL);
    
  return rv;
}
