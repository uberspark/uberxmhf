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

/* 
 * Author - Jim Newsome (jnewsome@no-fuss.com)
 */

#ifndef SEALED_CODE_PAL_PRIV_H
#define SEALED_CODE_PAL_PRIV_H

#include <tee-sdk/tv.h>
#include "sealed-code-pal.h"

/* addresses of these will be set by linker */
extern unsigned int __scode_start, __scode_end, __sdata_start, __sdata_end;

enum scp_command_t {
  SCP_SEAL=0,
  SCP_LOAD=1,
};

struct scp_in_msg {
  enum scp_command_t command;
  union {
    struct {
      uint8_t code[SCP_MAX_UNSEALED_LEN];
      size_t code_len;
    } seal;
    struct {
      uint8_t code[SCP_MAX_SEALED_LEN];
      size_t code_len;
      uint8_t params[SCP_MAX_PARAM_LEN];
      size_t params_len;
    } load;
  } m;
};

struct scp_out_msg {
  uint32_t status;
  /* when status == 0, returned msg has the
   * same type as input command. Otherwise undefined.
   */
  union {
    struct {
      uint8_t code[SCP_MAX_SEALED_LEN];
      size_t code_len;
    } seal;
    struct {
      uint8_t output[SCP_MAX_OUTPUT_LEN];
      size_t output_len;
    } load;
  } r;
};

void sealed_code_pal(struct scp_in_msg *in, size_t in_len,
                     struct scp_out_msg *out, size_t *out_len);
#endif
