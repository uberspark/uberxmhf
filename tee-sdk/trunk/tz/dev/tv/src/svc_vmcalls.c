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

#include "vmcalls.h"
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#include <trustvisor/tv_utpm.h>

int svc_utpm_seal(TPM_PCR_INFO *pcrInfo,
                  void *in,
                  size_t in_len,
                  void *out,
                  size_t *out_len)
{
  unsigned int inbuf1[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf1[2]= {(unsigned int)out, (unsigned int)out_len};

  return vmcall(TV_HC_UTPM_SEAL,
                (uint32_t)inbuf1,
                (uint32_t)pcrInfo,
                (uint32_t)outbuf1,
                0);
}

int svc_utpm_unseal(void *in,
                    size_t in_len,
                    void *out,
                    size_t *out_len)
{
  int ret;
  unsigned int inbuf2[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf2[2]= {(unsigned int)out, (unsigned int)out_len};

  return vmcall(TV_HC_UTPM_UNSEAL,
                (uint32_t)inbuf2,
                (uint32_t)outbuf2,
                0,
                0);
}

int svc_utpm_quote(TPM_NONCE *nonce,
                   TPM_PCR_SELECTION *tpmsel,
                   uint8_t *out,
                   size_t *out_len)
{
  int ret;
  unsigned int outbuf[2]= {(unsigned int)out, (unsigned int)out_len};

  return vmcall(TV_HC_UTPM_QUOTE,
                (uint32_t)tpmsel,
                (uint32_t)outbuf,
                (uint32_t)nonce,
                0);
}

int svc_utpm_pcr_extend(uint32_t idx,   /* in */
                        uint8_t *meas) /* in */
{
  return vmcall(TV_HC_UTPM_PCREXT,
                (uint32_t)idx,
                (uint32_t)meas,
                0,
                0);
}

int svc_utpm_id_getpub(uint8_t *N) /* out */
{
    return vmcall(TV_HC_UTPM_ID_GETPUB,
                  (uint32_t)N,
                  0,
                  0,
                  0);
}

int svc_utpm_pcr_read(uint32_t idx, /* in */
                      uint8_t *val) /* out */
{
  return vmcall(TV_HC_UTPM_PCRREAD,
                (uint32_t)idx,
                (uint32_t)val,
                0,
                0);
}

int svc_utpm_rand(void *out, /* out */
                  size_t *out_len) /* in,out */
{
  return vmcall(TV_HC_UTPM_GENRAND,
                (uint32_t)out,
                (uint32_t)out_len,
                0,
                0);
}
