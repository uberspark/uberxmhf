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

/* move into tee-sdk when stable */
#include <tee-sdk/tz.h>
#include "tze-pb.h"

tz_return_t tze_pb_invoke(const tze_pb_proto_t protos[],
                          uint32_t num_svcs,

                          tz_session_t *session,
                          uint32_t uiCommand,
                          const ProtobufCMessage *req,
                          ProtobufCMessage **res,
                          uint32_t *svc_err)
{
  tz_return_t tzerr=0;
  tz_operation_t op;
  void *res_packed;
  uint32_t res_packed_len;
  uint32_t req_packed_len;
  void *req_packed;

  *res=NULL;

  tzerr = TZOperationPrepareInvoke(session,
                                   uiCommand,
                                   NULL,
                                   &op);
  if (tzerr) {
    goto out;
  }

  req_packed_len = protobuf_c_message_get_packed_size(req);
  req_packed = TZEncodeArraySpace(&op, req_packed_len);
  if (!req_packed) {
    tzerr = TZDecodeGetError(&op);
    goto out;
  }

  protobuf_c_message_pack(req, req_packed);

  tzerr = TZOperationPerform(&op, svc_err);
  if (tzerr) {
    goto out;
  }

  res_packed = TZDecodeArraySpace(&op, &res_packed_len);
  if (!res_packed) {
    tzerr = TZDecodeGetError(&op);
    goto out;
  }

  *res = protobuf_c_message_unpack(protos[uiCommand].res_descriptor,
                                   NULL,
                                   res_packed_len,
                                   res_packed);

 out:
  TZOperationRelease(&op);
  return tzerr;
}
