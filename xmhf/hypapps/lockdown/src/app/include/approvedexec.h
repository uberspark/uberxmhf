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

//approved execution within trusted environment declarations/constants
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __APPROVEDEXEC_H__
#define __APPROVEDEXEC_H__

#define	MAX_FULL_HASHLIST_ELEMENTS		(75000)							//maximum no. of 20-byte SHA-1 records for
																		//full code-page hashes

#define	MAX_PARTIAL_HASHLIST_ELEMENTS	(15000)							//maximum no. of 20-byte SHA-1 records for
																		//partial code-page hashes


extern u32 ax_debug_flag;

//debugging macro for approvedexec module
#define AX_DEBUG(x) {if (ax_debug_flag) printf x;}

struct hashinfo {
	//char *name;
	//u32 pagenum;
	//u32 pagebase;
	u32 pageoffset;
	u32 size;
	u8  shanum[20];
} __attribute__((packed));

extern struct hashinfo hashlist[];
extern u32 hashlist_totalelements;

void approvedexec_setup(VCPU *vcpu, APP_PARAM_BLOCK *apb);
u32 approvedexec_checkhashes(u32 pagebase_paddr, u32 *index, u32 *fullhash);
u32 windows_verifycodeintegrity(VCPU *vcpu, u32 paddr, u32 vaddrfromcpu);
u32 approvedexec_handleevent(VCPU *vcpu, struct regs *r, 
  u64 gpa, u64 gva, u64 violationcode);


#endif //__APPROVEDEXEC_H__
