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
#include <tee-sdk/tzmarshal.h>
#include "tze-pb.h"

tze_pb_err_t tze_pb_svc(const tze_pb_proto_t protos[],
                        const tze_pb_imp_t imps[],
                        uint32_t num_svcs, 
                        uint32_t uiCommand, struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf)
{
  void *req_packed;
  uint32_t req_packed_len;
  ProtobufCMessage *req=NULL, *res=NULL;
  void *res_packed;
  uint32_t res_packed_len;
  tze_pb_err_t err = 0;
  tz_return_t tzerr;

  req_packed = TZIDecodeArraySpace(psInBuf, &req_packed_len);
  if(!req_packed) {
    tzerr = TZIDecodeGetError(psInBuf);
    err = TZE_PB_ETZ | (tzerr << 8);
    goto out;
  }

  req = protobuf_c_message_unpack(protos[uiCommand].req_descriptor, NULL, req_packed_len, req_packed);
  if(!req) {
    err = TZE_PB_EPB;
    goto out;
  }

  err = tze_pb_svc_msgs(protos, imps, num_svcs, 
                        uiCommand, req, &res);
  if(err) {
    goto free_unpacked_req;
  }

  res_packed_len = protobuf_c_message_get_packed_size(res);
  res_packed = TZIEncodeArraySpace(psOutBuf, res_packed_len);
  if(!res_packed) {
    tzerr = TZIDecodeGetError(psOutBuf);
    err = TZE_PB_ETZ | (tzerr << 8);
    goto free_res;
  }
  protobuf_c_message_pack(res, res_packed);
  
 free_res:
  if(imps[uiCommand].release_res) {
    imps[uiCommand].release_res(res);
  }
 free_unpacked_req:
  free(res);
  protobuf_c_message_free_unpacked(req, NULL);
 out:
  return err;
}

tze_pb_err_t tze_pb_svc_msgs(const tze_pb_proto_t protos[],
                             const tze_pb_imp_t imps[],
                             uint32_t num_svcs, 
                             uint32_t uiCommand,
                             const ProtobufCMessage *req,
                             ProtobufCMessage **res)
{
  tze_pb_err_t err = 0;
  uint32_t invoke_err;

  *res = malloc(protos[uiCommand].res_descriptor->sizeof_message);
  if(!*res) {
    err = TZE_PB_ENOMEM;
    goto out;
  }
  protobuf_c_message_init(protos[uiCommand].res_descriptor, *res);

  invoke_err = imps[uiCommand].execute(req, *res);
  if (invoke_err) {
    err = TZE_PB_EINVOKE | (invoke_err << 8);
  }
  
 out:
  return err;
}
