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

#ifndef AUDITED_KV_H
#define AUDITED_KV_H

#include <stddef.h>
#include <stdint.h>

#include <tee-sdk/tz.h>

#include "audited-kv-errs.h"

#define AKV_EPOCH_NONCE_MAX 256 /* FIXME - should pull from svcapi.h */
#define AKV_AUDIT_STRING_MAX 1000 /* FIXME - can we even specify this? */

typedef struct {
  tz_device_t   tzDevice;
  tz_session_t  tzPalSession;
  tz_uuid_t     tzSvcId;
} akv_ctx_t;
int akv_ctx_init(akv_ctx_t* ctx);
int akv_ctx_release(akv_ctx_t* ctx);

typedef struct {
  const uint8_t* audit_nonce;
  size_t audit_nonce_len;
  const char* audit_string;
  size_t audit_string_len;

  akv_ctx_t* akv_ctx;
  uint32_t cmd_id;
  tz_operation_t tzStartOp;
} akv_cmd_ctx_t;
void akv_cmd_ctx_release(akv_cmd_ctx_t *ctx);

int akv_db_add_begin(akv_ctx_t*  ctx,
                     akv_cmd_ctx_t*  cmd_ctx,
                     const char* key,
                     const char* val);
int akv_db_add_execute(akv_cmd_ctx_t* ctx,
                       const void* audit_token,
                       size_t audit_token_len);


int akv_begin_db_get(akv_ctx_t*  ctx,
                     uint8_t*    epoch_nonce,
                     size_t*     epoch_nonce_len,
                     uint64_t*   epoch_offset,
                     char*       audit_string,
                     size_t*     audit_string_len,
                     const char* key,
                     char*       val,
                     int         val_len);
#endif
