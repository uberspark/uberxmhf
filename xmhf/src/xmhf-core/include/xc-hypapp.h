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

// XMHF hypapp callback declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_HYPAPP_H__
#define __XMHF_HYPAPP_H__

#ifndef __ASSEMBLY__


//generic catch-all app return codes
#define APP_SUCCESS     		(0x1)
#define APP_ERROR				(0x0)

//emhf app constant definitions
#define APP_IOINTERCEPT_CHAIN   0xA0
#define APP_IOINTERCEPT_SKIP    0xA1
#define APP_INIT_SUCCESS        0x0
#define APP_INIT_FAIL           0xFF


//XMHF hypapp callback declarations 
//TODO: need to go into libxmhfcore dev headers
extern u32 xmhf_hypapp_initialization(context_desc_t context_desc, hypapp_env_block_t hypappenvb);
extern u32 xmhf_hypapp_handlehypercall(context_desc_t context_desc, u64 hypercall_id, u64 hypercall_param);	
extern u32 xmhf_hypapp_handleintercept_portaccess(context_desc_t context_desc, u32 portnum, u32 access_type, u32 access_size);  
extern u32 xmhf_hypapp_handleintercept_hwpgtblviolation(context_desc_t context_desc, u64 gpa, u64 gva, u64 error_code);
extern void xmhf_hypapp_handleshutdown(context_desc_t context_desc);


//XMHF hypapp callbacks referenced by the XMHF core
//note: these are the interfaces core uses to invoke hypapp callbacks
extern u32 xc_hypapp_initialization(context_desc_t context_desc, hypapp_env_block_t hypappenvb);
extern u32 xc_hypapp_handlehypercall(context_desc_t context_desc, u64 hypercall_id, u64 hypercall_param);	
extern u32 xc_hypapp_handleintercept_portaccess(context_desc_t context_desc, u32 portnum, u32 access_type, u32 access_size); 
extern u32 xc_hypapp_handleintercept_hwpgtblviolation(context_desc_t context_desc, u64 gpa, u64 gva, u64 error_code);
extern void xc_hypapp_handleshutdown(context_desc_t context_desc);


#endif	//__ASSEMBLY__

#endif	// __XMHF_HYPAPP_H__
