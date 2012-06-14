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
#include <tsvc.h>
#include <tee-sdk/tzmarshal.h>
#include "tze-pb.h"

static void* get_stderr(size_t *len)
{
  char *rv = malloc(4096);
  if(!rv) {
    return NULL;
  }
  *len = tsvc_read_stderr(rv, 4095);
  rv[*len] = '\0';
  return rv;
}

tz_return_t TZEDispatchImpProtobuf(const tze_pb_proto_t protos[],
                                   const tze_pb_imp_t imps[],
                                   uint32_t num_svcs,

                                   uint32_t uiCommand,
                                   struct tzi_encode_buffer_t *psInBuf,
                                   struct tzi_encode_buffer_t *psOutBuf,
                                   tz_return_t *puiRv)
{
  ProtobufCMessage *req=NULL, *res=NULL;
  tz_return_t tzerr=0;

  if (protos[uiCommand].req_descriptor) {
    tzerr = TZIDecodeProtobuf(psInBuf,
                              protos[uiCommand].req_descriptor,
                              NULL,
                              &req);
    if(tzerr) {
      goto out;
    }
  }

  tzerr = TZEDispatchImpProtobufMsgs(protos, imps, num_svcs, 
                                     uiCommand, req, &res, puiRv);
  {
    /* XXX Temp. this should be an independent layer */
    size_t len;
    void *buf;
    buf = get_stderr(&len);
    TZIEncodeArray(psOutBuf, buf, len);
    free(buf);
  }

  if(tzerr || *puiRv) {
    assert(!res);
    goto free_unpacked_req;
  }

  if (protos[uiCommand].res_descriptor) {
    tzerr = TZIEncodeProtobuf(psOutBuf, res);
    if(tzerr) {
      goto free_res;
    }
  }
  
 free_res:
  if(imps[uiCommand].release_res) {
    imps[uiCommand].release_res(res);
  }
  free(res);
 free_unpacked_req:
  if(req) {
    protobuf_c_message_free_unpacked(req, NULL);
  }
 out:
  return tzerr;
}

tz_return_t TZEDispatchImpProtobufMsgs(const tze_pb_proto_t protos[],
                                       const tze_pb_imp_t imps[],
                                       uint32_t num_svcs,

                                       uint32_t uiCommand,
                                       const ProtobufCMessage *req,
                                       ProtobufCMessage **res,
                                       tz_return_t *puiRv)
{
  return TZEExecuteProtobufFn(protos[uiCommand].res_descriptor,
                              imps[uiCommand].execute,
                              req,
                              res,
                              puiRv);
}

tz_return_t TZEExecuteProtobufFn(const ProtobufCMessageDescriptor *res_descr,
                                 tze_pb_execute_fn *exec,

                                 const ProtobufCMessage *req,
                                 ProtobufCMessage **res,
                                 tz_return_t *puiRv)
{
  tz_return_t err=0;

  if(res_descr && res) {
    *res = malloc(res_descr->sizeof_message);
    if(!*res) {
      err = TZ_ERROR_MEMORY;
      goto out;
    }
    protobuf_c_message_init(res_descr, *res);
  }

  if(res_descr) {
    *puiRv = exec(req, *res);
  } else {
    *puiRv = exec(req, NULL);
  }

  if (*puiRv && res) {
    /* Note that we interpret non-zero puiRv to mean there is no
       encodable result. In case the invoked function wants to return
       an error and additional information, puiRv should be 0, and the
       error + addtl info should be encoded in 'res' */
    free(*res);
    *res=NULL;
  }
  
 out:
  return err;
}
