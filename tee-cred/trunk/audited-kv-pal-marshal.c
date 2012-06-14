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

#include <string.h>

#include <tee-sdk/tzmarshal.h>

#include <google/protobuf-c/protobuf-c.h>

#include "proto-gend/audited.pb-c.h"
#include "audited-kv-pal.h"
#include "audited-kv-pal-fns.h"
#include "audited-kv-pal-storage.h"
#include "audited.h"

/* would be nice to extend protoc compiler to auto-generate this file
   this from service description */

static const tze_pb_imp_t akvp_imps[] = {
  [AKVP_INIT] = {
    .execute=(tze_pb_execute_fn*)akvp_init,
    .release_res=NULL,
  },
  [AKVP_START_AUDITED_CMD] = {
    .execute=(tze_pb_execute_fn*)audited_start_cmd,
    .release_res=NULL,
  },
  [AKVP_EXECUTE_AUDITED_CMD] = {
    .execute=(tze_pb_execute_fn*)audited_execute_cmd,
    .release_res=(tze_pb_release_res_fn*)audited_execute_cmd_release_res,
  },
  [AKVP_EXPORT] = {
    .execute=(tze_pb_execute_fn*)akvp_export,
    .release_res=(tze_pb_release_res_fn*)akvp_export_release_res,
  },
  [AKVP_IMPORT] = {
    .execute=(tze_pb_execute_fn*)akvp_import,
    .release_res=NULL,
  },
};

void audited_kv_pal(uint32_t uiCommand, struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
  tz_return_t rv;
  rv = TZEDispatchImpProtobuf(akvp_protos,
                              akvp_imps,
                              AKVP_NUM, 

                              uiCommand,
                              psInBuf,
                              psOutBuf,
                              puiRv);
  if (rv) {
    *puiRv = AKV_ETZ | (rv << 8);
  }
}
