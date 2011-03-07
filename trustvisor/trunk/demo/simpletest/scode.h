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

#include  "config.h"

#define  MAX_PARAMS_NUM 10
#define PARAMS_TYPE_INTEGER 1
#define PARAMS_TYPE_POINTER 2

#define  SECTION_TYPE_SCODE 1
#define  SECTION_TYPE_SDATA 2
#define  SECTION_TYPE_PARAM 3
#define  SECTION_TYPE_STACK 4
#define  SECTION_TYPE_STEXT 5
/* definde for scode sections info */
#define MAX_SECTION_NUM 10  /* max sections that are allowed in scode registration */
#define PAGE_SIZE 0x1000

//typedef int SECTION_TYPE;  /* section type, different section types have different page permission */

struct scode_params_struct{
    int type;  /* 1: integer ;  2:pointer*/
    int size;
};

struct scode_params_info{
   int params_num;
   struct scode_params_struct pm_str[MAX_PARAMS_NUM];
};

struct scode_sections_struct{
    int type;  
	unsigned int start_addr;
    int page_num;
};

struct scode_sections_info{
   int section_num;
   struct scode_sections_struct ps_str[MAX_SECTION_NUM];
};

enum VMMcmd
{
	VMM_REG = 1,
	VMM_UNREG = 2,
	VMM_SEAL =3,
	VMM_UNSEAL =4,
	VMM_QUOTE =5,
	VMM_TEST = 255,
};

#ifndef IS_VMX
static inline int scode_registration(unsigned int pageinfo, unsigned int params, unsigned int entry)
{
	int ret;
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_REG), "c"(pageinfo), "S"(params), "D"(entry));
}

static inline int scode_unregistration(unsigned int start)
{
	int ret;
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_UNREG), "c"(start));
}


static inline int scode_seal(unsigned int pcrAtRelease_addr, unsigned int inaddr, unsigned int inlen, unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  unsigned int inbuf1[2]= {inaddr,inlen};
  unsigned int outbuf1[2]= {outaddr, outlen_addr};

  __asm__ __volatile__(
                        "vmmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_SEAL), "c"((unsigned int)inbuf1), "d"(pcrAtRelease_addr), "S"((unsigned int)outbuf1));
}

static inline int scode_unseal(unsigned int inaddr, unsigned int inlen, unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  unsigned int inbuf2[2]= {inaddr,inlen};
  unsigned int outbuf2[2]= {outaddr, outlen_addr};

  __asm__ __volatile__(
                        "vmmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_UNSEAL), "c"((unsigned int)inbuf2), "d"((unsigned int)outbuf2));
}

static inline int scode_quote(unsigned int nonce_addr, unsigned int tpmsel_addr, unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  unsigned int outbuf[2]= {outaddr, outlen_addr};

  __asm__ __volatile__(
                        "vmmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_QUOTE), "S"(nonce_addr), "c"(tpmsel_addr), "d"((unsigned int)outbuf));
}

static inline int scode_test(void)
{
	int ret;
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_TEST));
}
#else
static inline int scode_test(void)
{
	int ret;
	__asm__ __volatile__(
			"vmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_TEST));
}

static inline int scode_registration(unsigned int pageinfo, unsigned int params, unsigned int entry)
{
	int ret;
	__asm__ __volatile__(
			"vmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_REG), "c"(pageinfo), "S"(params), "D"(entry));
}

static inline int scode_unregistration(unsigned int start)
{
	int ret;
	__asm__ __volatile__(
			"vmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_UNREG), "c"(start));
}

static inline int scode_seal(unsigned int pcrAtRelease_addr, unsigned int inaddr, unsigned int inlen, unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  unsigned int inbuf1[2]= {inaddr,inlen};
  unsigned int outbuf1[2]= {outaddr, outlen_addr};
  __asm__ __volatile__(
                        "vmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_SEAL), "c"((unsigned int)inbuf1),  "d"(pcrAtRelease_addr), "S"((unsigned int)outbuf1));
}

static inline int scode_unseal(unsigned int inaddr, unsigned int inlen, unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  unsigned int inbuf2[2]= {inaddr, inlen};
  unsigned int outbuf2[2]= {outaddr, outlen_addr};

  __asm__ __volatile__(
                        "vmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_UNSEAL), "c"((unsigned int)inbuf2), "d"((unsigned int)outbuf2));
}

static inline int scode_quote(unsigned int nonce_addr, unsigned int tpmsel_addr, unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  unsigned int outbuf[2]= {outaddr, outlen_addr};

  __asm__ __volatile__(
                        "vmcall\n\t"
			:"=a"(ret)
			: "a"(VMM_QUOTE), "S"(nonce_addr), "c"(tpmsel_addr), "d"((unsigned int)outbuf));
}
#endif
