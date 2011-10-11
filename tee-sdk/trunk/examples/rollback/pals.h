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

#include <stddef.h>
#include <stdint.h>

#include <tee-sdk/tzmarshal.h>

#include <trustvisor/tv_utpm.h>

#ifndef _PALS_H_
#define _PALS_H_

typedef enum {
  PAL_ARB_INITIALIZE,
  PAL_ARB_INCREMENT,
  PAL_NV_ROLLBACK,
  PAL_UNSEAL,
  PAL_SEAL,
  PAL_TEST,
} PAL_CMD;

/* Really simple state for demonstration purposes. */
typedef struct {
    uint64_t counter;
} pal_state_t;

/* Incoming request (from the above ENUM) */
typedef struct {
    uint32_t cmd;
} pal_request_t;


/* PAL entry point */
void pals(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv);
tz_return_t pal_seal(TPM_PCR_INFO *pcrInfo, uint8_t *input, uint32_t inputLen, uint8_t *output, size_t *outputLen);
tz_return_t pal_unseal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen, uint8_t *digestAtCreation);
tz_return_t pal_nv_rollback(IN uint8_t *newval,
                            OUT uint32_t *nv_size,
                            OUT uint8_t *oldval);


/* To avoid malloc(), just use a single global PAL state, statically allocated. */
extern pal_state_t g_pal_state;


#endif /* _PALS_H_ */
