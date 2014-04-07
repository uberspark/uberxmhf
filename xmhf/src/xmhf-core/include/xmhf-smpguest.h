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

// EMHF SMP guest component 
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_SMPGUEST_H__
#define __EMHF_SMPGUEST_H__

//bring in arch. specific declarations
#include <arch/xmhf-smpguest-arch.h>


#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//exported DATA 
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//rich guest memory functions

static inline bool xmhf_smpguest_readu16(context_desc_t context_desc, const void *guestaddress, u16 *valueptr){
		u16 *tmp = (u16 *)xmhf_smpguest_arch_walk_pagetables(context_desc, guestaddress);
		if((u32)tmp == 0xFFFFFFFFUL || valueptr == NULL)
			return false;
		//#ifdef __XMHF_VERIFICATION__
		//	*valueptr = nondet_u32();
		//#else
		//	*valueptr = *tmp;
		//#endif
		*valueptr = xmhfhw_sysmemaccess_readu16((u32)tmp);
		return true;
}

static inline bool xmhf_smpguest_writeu16(context_desc_t context_desc, const void *guestaddress, u16 value){
		u16 *tmp = (u16 *)xmhf_smpguest_arch_walk_pagetables(context_desc, guestaddress);
		if((u32)tmp == 0xFFFFFFFFUL || 
			( ((u32)tmp >= rpb->XtVmmRuntimePhysBase) && ((u32)tmp <= (rpb->XtVmmRuntimePhysBase+rpb->XtVmmRuntimeSize)) ) 
		  )
			return false;
		//#ifndef __XMHF_VERIFICATION__
		//*tmp = value;
		//#endif
		xmhfhw_sysmemaccess_writeu16((u32)tmp, value);
		return true;
}

static inline bool xmhf_smpguest_memcpyfrom(context_desc_t context_desc, void *buffer, const void *guestaddress, size_t numbytes){
	u8 *guestbuffer = (u8 *)xmhf_smpguest_arch_walk_pagetables(context_desc, guestaddress);
	if((u32)guestbuffer == 0xFFFFFFFFUL)
		return false;
	//#ifndef __XMHF_VERIFICATION__
	//memcpy(buffer, gpa2hva(guestbuffer), numbytes);
	//#endif
	xmhfhw_sysmemaccess_copy(buffer, gpa2hva(guestbuffer), numbytes);
}

static inline bool xmhf_smpguest_memcpyto(context_desc_t context_desc, void *guestaddress, const void *buffer, size_t numbytes){
	u8 *guestbuffer = (u8 *)xmhf_smpguest_arch_walk_pagetables(context_desc, guestaddress);
	if((u32)guestbuffer == 0xFFFFFFFFUL || 
		( ((u32)guestbuffer >= rpb->XtVmmRuntimePhysBase) && ((u32)guestbuffer <= (rpb->XtVmmRuntimePhysBase+rpb->XtVmmRuntimeSize)) ) 
	  )
		return false;
	//#ifndef __XMHF_VERIFICATION__
	//memcpy(gpa2hva(guestbuffer), buffer, numbytes);
	//#endif
	xmhfhw_sysmemaccess_copy(gpa2hva(guestbuffer), buffer, numbytes);
}



//initialize SMP guest logic
//void xmhf_smpguest_initialize(VCPU *vcpu);
void xmhf_smpguest_initialize(context_desc_t context_desc);

//quiesce interface to switch all guest cores into hypervisor mode
//void xmhf_smpguest_quiesce(VCPU *vcpu);

//endquiesce interface to resume all guest cores after a quiesce
//void xmhf_smpguest_endquiesce(VCPU *vcpu);

//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_walk_pagetables(context_desc_t context_desc, u32 vaddr);



#endif	//__ASSEMBLY__

#endif //__EMHF_SMPGUEST_H__
