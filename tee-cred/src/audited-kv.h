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

#ifndef AUDITED_KV_H
#define AUDITED_KV_H

#include <stddef.h>
#include <stdint.h>

#include <tee-sdk/tz.h>
#include <tee-sdk/tze.h>

#include "proto-gend/audited.pb-c.h"
#include "audited-kv-errs.h"

typedef struct {
  tze_dev_svc_sess_t tz_sess;
} akv_ctx_t;
akv_err_t akv_ctx_init(akv_ctx_t* ctx);
akv_err_t akv_ctx_release(akv_ctx_t* ctx);
akv_err_t akv_new(akv_ctx_t* ctx, const char* priv_key_pem);
akv_err_t akv_export(akv_ctx_t* ctx,
                     uint8_t **data,
                     size_t *data_len);
akv_err_t akv_import(akv_ctx_t* ctx,
                     uint8_t *data,
                     size_t data_len);

typedef struct {
  Audited__StartRes__Res *audited;

  akv_ctx_t* akv_ctx;
} akv_cmd_ctx_t;
void akv_cmd_ctx_release(akv_cmd_ctx_t *ctx);

akv_err_t akv_db_add_begin(akv_ctx_t*  ctx,
                           akv_cmd_ctx_t*  cmd_ctx,
                           const char* key,
                           const void* val,
                           size_t val_len);
akv_err_t akv_db_add_execute(akv_cmd_ctx_t* ctx,
                             const void* audit_token,
                             size_t audit_token_len);

akv_err_t akv_db_get_begin(akv_ctx_t*  ctx,
                           akv_cmd_ctx_t* cmd_ctx,
                           const char* key);
akv_err_t akv_db_get_execute(akv_cmd_ctx_t* ctx,
                             const void* audit_token,
                             size_t audit_token_len,
                             void **val,
                             size_t *val_len);


#endif
