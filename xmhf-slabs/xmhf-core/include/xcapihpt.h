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
 *
 *  XMHF core API
 *
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __XCAPIHPT_H__
#define __XCAPIHPT_H__


// memory protection types
#define MEMP_PROT_NOTPRESENT	(1)	// page not present
#define	MEMP_PROT_PRESENT		(2)	// page present
#define MEMP_PROT_READONLY		(4)	// page read-only
#define MEMP_PROT_READWRITE		(8) // page read-write
#define MEMP_PROT_EXECUTE		(16) // page execute
#define MEMP_PROT_NOEXECUTE		(32) // page no-execute
#define MEMP_PROT_MAXVALUE		(MEMP_PROT_NOTPRESENT+MEMP_PROT_PRESENT+MEMP_PROT_READONLY+MEMP_PROT_READWRITE+MEMP_PROT_NOEXECUTE+MEMP_PROT_EXECUTE)


#ifndef __ASSEMBLY__

///////////////////////////////////////////////////////////////////////////////
//HPT related core APIs
void xc_api_hpt_setprot(context_desc_t context_desc, u64 gpa, u32 prottype);
void xc_api_hpt_arch_setprot(context_desc_t context_desc, u64 gpa, u32 prottype);

u32 xc_api_hpt_getprot(context_desc_t context_desc, u64 gpa);
u32 xc_api_hpt_arch_getprot(context_desc_t context_desc, u64 gpa);

void xc_api_hpt_setentry(context_desc_t context_desc, u64 gpa, u64 entry);
void xc_api_hpt_arch_setentry(context_desc_t context_desc, u64 gpa, u64 entry);

u64 xc_api_hpt_getentry(context_desc_t context_desc, u64 gpa);
u64 xc_api_hpt_arch_getentry(context_desc_t context_desc, u64 gpa);

void xc_api_hpt_flushcaches(context_desc_t context_desc);
void xc_api_hpt_arch_flushcaches(context_desc_t context_desc);

u64 xc_api_hpt_lvl2pagewalk(context_desc_t context_desc, u64 gva);
u64 xc_api_hpt_arch_lvl2pagewalk(context_desc_t context_desc, u64 gva);

void xc_api_hpt_arch_establishshape(u32 partition_index);
u64 xc_api_hpt_arch_gethptroot(context_desc_t context_desc);


#endif	//__ASSEMBLY__


#endif //__XCAPIHPT_H__
