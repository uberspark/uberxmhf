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

#ifndef AUDITED_KV_PAL
#define AUDITED_KV_PAL

#include <stdint.h>
#include <stdbool.h>

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include "tze-pb.h"

#include "audited-kv-errs.h"

enum akvp_cmds {
  AKVP_INIT=0,            /* audit-pubkey, password -> () */
  AKVP_START_AUDITED_CMD=1,
  AKVP_EXECUTE_AUDITED_CMD=2,

  AKVP_NUM=3,
};
  /* AKVP_AUDIT_GET_NONCE, /\* ()                -> random nonce *\/ */
  /* AKVP_AUDIT_EXECUTE,   /\* random nonce, cmd -> f(cmd) *\/ */

  /* AKVP_DB_ADD,          /\* key, val          -> ()  *\/ */
  /* AKVP_DB_GET,          /\* key               -> val *\/ */
  /* AKVP_DB_DEL,          /\* key               -> () *\/ */
  /* AKVP_DB_EXPORT,       /\* ()                -> seal(db) *\/ */
  /* AKVP_DB_IMPORT,       /\* seal(db)          -> () *\/ */
  /* AKVP_DB_MIGRATE,      /\* dest-pubkey, cert-chain -> E(db) *\/ */
  
  /* AKVP_PW_LOCK,         /\* ()                -> () *\/ */
  /* AKVP_PW_UNLOCK,       /\* password          -> () *\/ */
  /* AKVP_PW_CHANGE,       /\* oldpass, newpass  -> () *\/ */
/* }; */

extern const tze_pb_proto_t akvp_protos[];

void audited_kv_pal(uint32_t uiCommand, struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv);

#endif
