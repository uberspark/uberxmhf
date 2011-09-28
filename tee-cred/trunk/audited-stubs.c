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

#include <stdlib.h>
#include "audited-stubs.h"
#include "audited-kv-pal.h"
#include "proto-gend/audited.pb-c.h"

tze_pb_err_t audited_invoke(tz_session_t *session,
                            uint32_t uiCommand,
                            const ProtobufCMessage *req,
                            ProtobufCMessage **res,
                            uint32_t *svc_err)
{
  return tze_pb_invoke(audited_protos,
                       AKVP_NUM,

                       session,
                       uiCommand,
                       req,
                       res,
                       svc_err);
}

tze_pb_err_t audited_invoke_start(tz_session_t *session,
                                  uint32_t audited_cmd,
                                  const ProtobufCMessage *audited_req,
                                  Audited__StartRes **start_res,
                                  uint32_t *audited_err)
{
  Audited__StartReq start_req;
  size_t audited_req_packed_len;
  void *audited_req_packed=NULL;
  tze_pb_err_t rv;

  audited_req_packed_len = protobuf_c_message_get_packed_size(audited_req);
  audited_req_packed = malloc(audited_req_packed_len);
  if(!audited_req_packed) {
    abort();
  }
  protobuf_c_message_pack(audited_req, audited_req_packed);

  start_req = (Audited__StartReq) {
    .base = PROTOBUF_C_MESSAGE_INIT (&audited__start_req__descriptor),
    .cmd = audited_cmd,
    .cmd_input = (ProtobufCBinaryData) {
      .data = audited_req_packed,
      .len = audited_req_packed_len,
    }
  };

  rv = audited_invoke(session,
                      AKVP_START_AUDITED_CMD,
                      (ProtobufCMessage*)&start_req,
                      (ProtobufCMessage**)start_res,
                      audited_err);

  free(audited_req_packed);
  return rv;
}
