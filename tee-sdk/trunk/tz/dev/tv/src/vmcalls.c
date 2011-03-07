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

#include "scode.h"
#include "svcapi.h"

#include <stdint.h>

__attribute__ ((section (".stext")))
int scode_seal(uint8_t *pcrAtRelease_addr,
               void *in,
               size_t in_len,
               void *out,
               size_t *out_len)
{
  int ret;
  unsigned int inbuf1[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf1[2]= {(unsigned int)out, (unsigned int)out_len};

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_SEAL), "c"((unsigned int)inbuf1), "d"(pcrAtRelease_addr), "S"((unsigned int)outbuf1));
  return ret;
}

__attribute__ ((section (".stext")))
int scode_unseal(void *in,
                 size_t in_len,
                 void *out,
                 size_t *out_len)
{
  int ret;
  unsigned int inbuf2[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf2[2]= {(unsigned int)out, (unsigned int)out_len};

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_UNSEAL), "c"((unsigned int)inbuf2), "d"((unsigned int)outbuf2));
  return ret;
}

__attribute__ ((section (".stext")))
int scode_quote(uint8_t *nonce,
                uint32_t *tpmsel,
                uint8_t *out,
                size_t *out_len)
{
  int ret;
  unsigned int outbuf[2]= {(unsigned int)out, (unsigned int)out_len};

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_QUOTE), "S"(nonce), "c"(tpmsel), "d"((unsigned int)outbuf));
  return ret;
}

int scode_register(const struct scode_sections_info *pageinfo,
                   const struct scode_params_info *params,
                   const void *entry)
{
  int ret;
  lock_scode_pages(pageinfo);

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_REG), "c"((unsigned int)pageinfo), "S"((unsigned int)params), "D"((unsigned int)entry));

  return ret;
}

int scode_unregister(void *entry)
{
  int ret;
  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_UNREG), "c"(entry));
  return ret;
}

int scode_test(void)
{
  int ret;
  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_TEST));
  return ret;
}

