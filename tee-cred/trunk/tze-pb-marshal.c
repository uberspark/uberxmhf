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

#include <tee-sdk/tzmarshal.h>

#include "tze-pb.h"

tz_return_t TZIDecodeProtobuf(tzi_encode_buffer_t *tz_buf,
                              const ProtobufCMessageDescriptor *pb_desc,
                              ProtobufCAllocator *pb_alloc,
                              ProtobufCMessage **pb_msg)
{
  void *pb_packed;
  uint32_t pb_packed_len;

  if(TZIDecodeGetError(tz_buf)) {
    goto out;
  }

  *pb_msg=NULL;

  pb_packed = TZIDecodeArraySpace(tz_buf, &pb_packed_len);
  if(!pb_packed) {
    assert(TZIDecodeGetError(tz_buf) != 0);
    goto out;
  }

  *pb_msg = protobuf_c_message_unpack(pb_desc,
                                      pb_alloc,
                                      pb_packed_len,
                                      pb_packed);
  if(!*pb_msg) {
    /* add custom error instead? */
    tz_buf->uiRetVal = TZ_ERROR_ENCODE_FORMAT;
    goto out; 
  }

 out:
  return TZIDecodeGetError(tz_buf);
}

tz_return_t TZIEncodeProtobuf(tzi_encode_buffer_t *tz_buf,
                              const ProtobufCMessage *pb_msg)
                              
{
  void *pb_packed;
  uint32_t pb_packed_len;
  uint32_t pb_packed_len2;

  if(TZIDecodeGetError(tz_buf)) {
    goto out;
  }

  pb_packed_len = protobuf_c_message_get_packed_size(pb_msg);

  pb_packed = TZIEncodeArraySpace(tz_buf, pb_packed_len);
  if(!pb_packed) {
    assert(TZIDecodeGetError(tz_buf) != 0);
    return TZIDecodeGetError(tz_buf);
  }

  pb_packed_len2 = protobuf_c_message_pack(pb_msg, pb_packed);
  if(pb_packed_len2 != pb_packed_len) {
    /* add custom error instead? */
    tz_buf->uiRetVal = TZ_ERROR_ENCODE_FORMAT;
    goto out; 
  }

 out:
  return TZIDecodeGetError(tz_buf);
}
