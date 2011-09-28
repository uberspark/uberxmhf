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
#ifndef TZE_PB_H
#define TZE_PB_H

#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>
#include <google/protobuf-c/protobuf-c.h>

typedef enum {
  TZE_PB_ETZ=1, /* TZ error is shifted on */
  TZE_PB_EPB=2,
  TZE_PB_EINVOKE=3, /* invoke error is shifted on */
  TZE_PB_ENOMEM=4,
} tze_pb_err_t;

typedef int (tze_pb_execute_fn)(const ProtobufCMessage *, ProtobufCMessage *);
typedef void (tze_pb_release_res_fn)(ProtobufCMessage *);

typedef struct {
  tze_pb_execute_fn *execute;
  tze_pb_release_res_fn *release_res;
} tze_pb_imp_t;

typedef struct {
  const ProtobufCMessageDescriptor *req_descriptor;
  const ProtobufCMessageDescriptor *res_descriptor;
  const ProtobufCMessageDescriptor *err_descriptor;
} tze_pb_proto_t;

tze_pb_err_t tze_pb_svc(const tze_pb_proto_t protos[],
                        const tze_pb_imp_t imps[],
                        uint32_t num_svcs, 
                        uint32_t uiCommand,
                        struct tzi_encode_buffer_t *psInBuf,
                        struct tzi_encode_buffer_t *psOutBuf);

/* *res is malloc'd and must be freed */
tze_pb_err_t tze_pb_svc_msgs(const tze_pb_proto_t protos[],
                             const tze_pb_imp_t imps[],
                             uint32_t num_svcs, 
                             uint32_t uiCommand,
                             const ProtobufCMessage *req,
                             ProtobufCMessage **res);

/* call protobuf_c_message_free_unpacked on returned *res (if not
   NULL) */
tze_pb_err_t tze_pb_invoke(const tze_pb_proto_t protos[],
                           uint32_t num_svcs,
                           tz_session_t *session,
                           uint32_t uiCommand,
                           const ProtobufCMessage *req,
                           ProtobufCMessage **res,
                           uint32_t *svc_err);


#endif
