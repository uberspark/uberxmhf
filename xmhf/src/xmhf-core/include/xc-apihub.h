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
 * 	xmhf-apihub.h
 * 
 *  XMHF core API interface component declarations/definitions
 * 
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __XMHF_APIHUB_H__
#define __XMHF_APIHUB_H__

//hypapp callbacks
#define XMHF_APIHUB_HYPAPPCB_MAIN					(0)
#define XMHF_APIHUB_HYPAPPCB_HYPERCALL				(1)
#define XMHF_APIHUB_HYPAPPCB_SHUTDOWN				(2)
#define XMHF_APIHUB_HYPAPPCB_HWPGTBLVIOLATION		(3)
#define XMHF_APIHUB_HYPAPPCB_PORTACCESS				(4)

//core APIs
#define	XMHF_APIHUB_COREAPI_OUTPUTDEBUGSTRING			(0)
#define XMHF_APIHUB_COREAPI_REBOOT						(1)
#define XMHF_APIHUB_COREAPI_SETMEMPROT					(2)
#define XMHF_APIHUB_COREAPI_MEMPROT_GETPROT				(3)
#define XMHF_APIHUB_COREAPI_MEMPROT_FLUSHMAPPINGS		(4)
#define XMHF_APIHUB_COREAPI_SMPGUEST_WALK_PAGETABLES	(5)
#define XMHF_APIHUB_COREAPI_BASEPLATFORM_GETCPUTABLE	(15)
#define XMHF_APIHUB_COREAPI_MEMPROT_SETSINGULARHPT		(16)
#define XMHF_APIHUB_COREAPI_MEMPROT_GETHPTROOT			(17)
#define XMHF_APIHUB_COREAPI_HPT_SETENTRY				(18)
#define XMHF_APIHUB_COREAPI_HYPAPPCBRETURN				(0xFFFF)


#ifndef __ASSEMBLY__

//hypapp parameter block
typedef struct {
	u64 param1;
	u64 param2;
	u64 param3;
	u64 param4;
	u64 param5;
	u64 param6;
	u64 param7;
	u64 param8;
	u64 result;
	context_desc_t context_desc;
	hypapp_env_block_t hypappenvb;
	xmhfcoreapiretval_t retval;
} __attribute__((packed)) XMHF_HYPAPP_PARAMETERBLOCK;

// declare paramcore and paramhypapp variables (which are defined in
// (xc.lds.S)
extern u8 paramcore_start[];
extern u8 paramhypapp_start[];

// declare core and hypapp parameter blocks which are initialized over
// the above two memory regions
extern XMHF_HYPAPP_PARAMETERBLOCK *paramcore;
extern XMHF_HYPAPP_PARAMETERBLOCK *paramhypapp;

//hypapp callback hub entry point and hypapp top of stack
extern u32 hypapp_cbhub_pc;
extern u32 hypapp_tos;

extern XMHF_HYPAPP_HEADER *g_hypappheader;

void xmhfcore_outputdebugstring(const char *s);
void xmhfcore_reboot(context_desc_t context_desc);
void xmhfcore_setmemprot(context_desc_t context_desc, u64 gpa, u32 prottype);
void xmhfcore_memprot_flushmappings(context_desc_t context_desc);
u8 * xmhfcore_smpguest_walk_pagetables(context_desc_t context_desc, u32 vaddr);
void xmhfcore_memprot_setsingularhpt(u64 hpt);
u64 xmhfcore_memprot_getHPTroot(context_desc_t context_desc);
void xmhfcore_memprot_hpt_setentry(context_desc_t context_desc, u64 hpt_paddr, u64 entry);

//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------
void xmhf_apihub_initialize (void);
void xmhf_apihub_fromhypapp(u32 callnum);

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------
void xmhf_apihub_arch_initialize(void);
void xmhf_apihub_arch_tohypapp(u32 hypappcallnum);


#endif	//__ASSEMBLY__

#endif //__XMHF_APIHUB_H__
