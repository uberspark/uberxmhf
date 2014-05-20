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

// XMHF rich guest -- runtime portion x86 (VMX) backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf-core.h> 
#include <xc-x86.h>
#include <xc-x86vmx.h>


//handle guest memory reporting (via INT 15h redirection)
struct regs xmhf_smpguest_arch_x86vmx_handle_guestmemoryreporting(context_desc_t context_desc, struct regs r){
	u16 cs, ip;
	u16 guest_flags;
	xc_hypapp_arch_param_t ap;
	xc_hypapp_arch_param_x86vmx_cpustate_desc_t desc;
	xc_hypapp_arch_param_x86vmx_cpustate_activity_t activity;
	
	ap = xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC);
	desc = ap.param.desc;
	ap = xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY);
	activity = ap.param.activity;

	//if E820 service then...
	if((u16)r.eax == 0xE820){
		//AX=0xE820, EBX=continuation value, 0 for first call
		//ES:DI pointer to buffer, ECX=buffer size, EDX='SMAP'
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
		printf("\nCPU(0x%02x): INT 15(e820): AX=0x%04x, EDX=0x%08x, EBX=0x%08x, ECX=0x%08x, ES=0x%04x, DI=0x%04x", context_desc.cpu_desc.cpu_index, 
		(u16)r.eax, r.edx, r.ebx, r.ecx, (u16)desc.es.selector, (u16)r.edi);
		
		if( (r.edx == 0x534D4150UL) && (r.ebx < xcbootinfo->memmapinfo_numentries) ){
			
			//copy the E820 descriptor and return its size
			if(!xmhf_smpguest_memcpyto(context_desc, (const void *)((u32)(desc.es.base+(u16)r.edi)), (void *)&xcbootinfo->memmapinfo_buffer[r.ebx], sizeof(GRUBE820)) ){
				printf("\n%s: Error in copying e820 descriptor to guest. Halting!", __FUNCTION__);
				HALT();
			}	
				
			r.ecx=20;

			//set EAX to 'SMAP' as required by the service call				
			r.eax=r.edx;

			//we need to update carry flag in the guest EFLAGS register
			//however since INT 15 would have pushed the guest FLAGS on stack
			//we cannot simply reflect the change by modifying vmcb->rflags
			//instead we need to make the change to the pushed FLAGS register on
			//the guest stack. the real-mode IRET frame looks like the following 
			//when viewed at top of stack
			//guest_ip		(16-bits)
			//guest_cs		(16-bits)
			//guest_flags (16-bits)
			//...
		
			//grab guest eflags on guest stack
			if(!xmhf_smpguest_readu16(context_desc, (const void *)((u32)desc.ss.base + (u16)r.esp + 0x4), &guest_flags)){
				printf("\n%s: Error in reading guest_flags. Halting!", __FUNCTION__);
				HALT();
			}
	
			//increment e820 descriptor continuation value
			r.ebx=r.ebx+1;
					
			if(r.ebx > (xcbootinfo->memmapinfo_numentries-1) ){
				//we have reached the last record, so set CF and make EBX=0
				r.ebx=0;
				guest_flags |= (u16)EFLAGS_CF;
			}else{
				//we still have more records, so clear CF
				guest_flags &= ~(u16)EFLAGS_CF;
			}

			//write updated eflags in guest stack
			if(!xmhf_smpguest_writeu16(context_desc, (const void *)((u32)desc.ss.base + (u16)r.esp + 0x4), guest_flags)){
				printf("\n%s: Error in updating guest_flags. Halting!", __FUNCTION__);
				HALT();
			}
			  
			
		}else{	//invalid state specified during INT 15 E820, halt
				printf("\nCPU(0x%02x): INT15 (E820), invalid state specified by guest. Halting!", context_desc.cpu_desc.cpu_index);
				HALT();
		}
		
		//update RIP to execute the IRET following the VMCALL instruction
		//effectively returning from the INT 15 call made by the guest
		activity.rip+=3;
		ap.param.activity = activity;
		ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
		xc_api_cpustate_set(context_desc, ap);
	
		return r;
	} //E820 service
	
	//ok, this is some other INT 15h service, so simply chain to the original
	//INT 15h handler

	//read the original INT 15h handler which is stored right after the VMCALL instruction
	if(!xmhf_smpguest_readu16(context_desc, 0x4AC+0x4, &ip) || !xmhf_smpguest_readu16(context_desc, 0x4AC+0x6, &cs)){
		printf("\n%s: Error in reading original INT 15h handler. Halting!", __FUNCTION__);
		HALT();
	}
	
	//update VMCS with the CS and IP and let go
	activity.rip = ip;
	ap.param.activity = activity;
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
	xc_api_cpustate_set(context_desc, ap);
	desc.cs.base = (cs *16);
	desc.cs.selector = cs;
	ap.param.desc = desc;
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC;
	xc_api_cpustate_set(context_desc, ap);
	
	return r;
}



bool xmhf_smpguest_arch_readu16(context_desc_t context_desc, const void *guestaddress, u16 *valueptr){
		u16 *tmp = (u16 *)xc_api_hpt_lvl2pagewalk(context_desc, guestaddress);
		if((u32)tmp == 0xFFFFFFFFUL || valueptr == NULL)
			return false;
		*valueptr = xmhfhw_sysmemaccess_readu16((u32)tmp);
		return true;
}

bool xmhf_smpguest_arch_writeu16(context_desc_t context_desc, const void *guestaddress, u16 value){
		u16 *tmp = (u16 *)xc_api_hpt_lvl2pagewalk(context_desc, guestaddress);
		if((u32)tmp == 0xFFFFFFFFUL || 
			( ((u32)tmp >= xcbootinfo->physmem_base) && ((u32)tmp <= (xcbootinfo->physmem_base+xcbootinfo->size)) ) 
		  )
			return false;
		xmhfhw_sysmemaccess_writeu16((u32)tmp, value);
		return true;
}

bool xmhf_smpguest_arch_memcpyfrom(context_desc_t context_desc, void *buffer, const void *guestaddress, size_t numbytes){
	u8 *guestbuffer = (u8 *)xc_api_hpt_lvl2pagewalk(context_desc, guestaddress);
	if((u32)guestbuffer == 0xFFFFFFFFUL)
		return false;
	xmhfhw_sysmemaccess_copy(buffer, gpa2hva(guestbuffer), numbytes);
}

bool xmhf_smpguest_arch_memcpyto(context_desc_t context_desc, void *guestaddress, const void *buffer, size_t numbytes){
	u8 *guestbuffer = (u8 *)xc_api_hpt_lvl2pagewalk(context_desc, guestaddress);
	if((u32)guestbuffer == 0xFFFFFFFFUL || 
		( ((u32)guestbuffer >= xcbootinfo->physmem_base) && ((u32)guestbuffer <= (xcbootinfo->physmem_base+xcbootinfo->size)) ) 
	  )
		return false;
	xmhfhw_sysmemaccess_copy(gpa2hva(guestbuffer), buffer, numbytes);
}



