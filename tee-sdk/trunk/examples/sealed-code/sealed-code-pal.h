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

#ifndef SEALED_CODE_PAL_H
#define SEALED_CODE_PAL_H

/* system */
#include <stdint.h>
#include <stddef.h>

typedef void (*scp_sealed_fn_t)(uint8_t *in, size_t in_len, uint8_t *out, size_t *out_len);

/* #define SCP_MAX_UNSEALED_LEN (10*PAGE_SIZE) */
/* #define SCP_MAX_SEALED_LEN (10*PAGE_SIZE) */
/* #define SCP_MAX_PARAM_LEN (1*PAGE_SIZE) */
/* #define SCP_MAX_OUTPUT_LEN (1*PAGE_SIZE) */
#define SCP_MAX_UNSEALED_LEN (200)
#define SCP_MAX_SEALED_LEN (200)
#define SCP_MAX_PARAM_LEN (200)
#define SCP_MAX_OUTPUT_LEN (200)

size_t scp_sealed_size_of_unsealed_size(size_t in);
void scp_register(void);
void scp_unregister(void);
int scp_seal(uint8_t *incode, size_t incode_len, uint8_t *outcode, size_t *outcode_len);
int scp_run(uint8_t *incode, size_t incode_len,
            uint8_t *params, size_t params_len,
            uint8_t *output, size_t *output_len);


#endif
