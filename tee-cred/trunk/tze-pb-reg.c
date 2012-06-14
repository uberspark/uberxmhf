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

/* move into tee-sdk when stable */
#include <unistd.h>
#include <tee-sdk/tz.h>
#include "tze-pb.h"

tz_return_t TZEDecodeProtobuf(tz_operation_t *psOperation,
                              const ProtobufCMessageDescriptor *pb_desc,
                              ProtobufCAllocator *pb_alloc,
                              ProtobufCMessage **pb_msg)
{
  void *pb_packed;
  uint32_t pb_packed_len;

  if(TZDecodeGetError(psOperation)) {
    goto out;
  }

  *pb_msg=NULL;

  pb_packed = TZDecodeArraySpace(psOperation, &pb_packed_len);
  if(!pb_packed) {
    assert(TZDecodeGetError(psOperation));
    goto out;
  }

  *pb_msg = protobuf_c_message_unpack(pb_desc,
                                      pb_alloc,
                                      pb_packed_len,
                                      pb_packed);
  if(!*pb_msg) {
    /* add custom error instead? */
    psOperation->sImp.psEncodeBuffer->uiRetVal = TZ_ERROR_ENCODE_FORMAT;
    goto out; 
  }

 out:
  return TZDecodeGetError(psOperation);
}

tz_return_t TZEEncodeProtobuf(tz_operation_t* psOperation,
                              const ProtobufCMessage *pb_msg)
{
  uint32_t pb_buf_len, pb_buf_len2;
  void *pb_buf;

  if (TZDecodeGetError(psOperation)) {
    goto out;
  }

  pb_buf_len = protobuf_c_message_get_packed_size(pb_msg);
  pb_buf = TZEncodeArraySpace(psOperation, pb_buf_len);
  if (!pb_buf) {
    assert(TZDecodeGetError(psOperation));
    goto out;
  }

  pb_buf_len2 = protobuf_c_message_pack(pb_msg, pb_buf);
  if (pb_buf_len2 != pb_buf_len) {
    psOperation->sImp.psEncodeBuffer->uiRetVal = TZ_ERROR_ENCODE_FORMAT;
    goto out;
  }

 out:
  return TZDecodeGetError(psOperation);
}
                  
tz_return_t TZEDispatchProtobuf(const tze_pb_proto_t protos[],
                                uint32_t num_svcs,

                                tz_session_t *session,
                                uint32_t uiCommand,
                                const ProtobufCMessage *req,
                                ProtobufCMessage **res,
                                tz_return_t *puiRv)
{
  tz_return_t tzerr=0;
  tz_operation_t op;

  if(res) {
    *res=NULL;
  }

  tzerr = TZOperationPrepareInvoke(session,
                                   uiCommand,
                                   NULL,
                                   &op);
  if (tzerr) {
    goto out;
  }

  if(protos[uiCommand].req_descriptor) {
    tzerr = TZEEncodeProtobuf(&op, req);
    if (tzerr) {
      goto out;
    }
  }

  tzerr = TZOperationPerform(&op, puiRv);
  { /* XXX TEMP. this should be an independent layer */
    void *buf=NULL;
    size_t len;
    buf = TZDecodeArraySpace(&op, &len);
    if(buf) {
      while(len) {
        size_t n;
        n = write(2, buf, len);
        if (n <= 0)
          break;
        len-=n;
      }
    }
  }
  if (tzerr) {
    goto out;
  }

  if(protos[uiCommand].res_descriptor) {
    tzerr = TZEDecodeProtobuf(&op,
                              protos[uiCommand].res_descriptor,
                              NULL,
                              res);
  }
  if (tzerr) {
    goto out;
  }

 out:
  TZOperationRelease(&op);
  return tzerr;
}
