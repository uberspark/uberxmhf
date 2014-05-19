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

// smpg-x86vmx - EMHF SMP guest component x86 (VMX) backend
// implementation
// author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf-core.h> 
#include <xc-x86.h>
#include <xc-x86vmx.h>



/*//---function to obtain the xc_cpu of the currently executing core----------------
//XXX: move this into baseplatform as backend
//note: this always returns a valid VCPU pointer
static xc_cpu_t *_vmx_getxc_cpu(void){

#ifndef __XMHF_VERIFICATION__

  int i;
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;
  
  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
  eax &= (u32)0xFFFFF000UL;
  lapic_reg = (u32 *)((u32)eax+ (u32)LAPIC_ID);
  lapic_id = *lapic_reg;
  //printf("\n%s: lapic base=0x%08x, id reg=0x%08x", __FUNCTION__, eax, lapic_id);
  lapic_id = lapic_id >> 24;
  //printf("\n%s: lapic_id of core=0x%02x", __FUNCTION__, lapic_id);
  
  for(i=0; i < (int)g_xc_cpu_count; i++){
    if(g_xc_cputable[i].cpuid == lapic_id)
        return( (xc_cpu_t *)&g_xc_cpu[g_xc_cputable[i].cpu_index] );
  }

  printf("\n%s: fatal, unable to retrieve xc_cpu for id=0x%02x", __FUNCTION__, lapic_id);
  HALT();
  return NULL; // currently unreachable 

#else //__XMHF_VERIFICATION

	//verification is always done in the context of a single core and xc_cpu/midtable is 
	//populated by the verification driver
	//TODO: LAPIC hardware modeling and moving this function as a public

#endif //__XMHF_VERIFICATION

  
}
*/


//----------------------------------------------------------------------





//handle guest memory reporting (via INT 15h redirection)
struct regs xmhf_smpguest_arch_x86vmx_handle_guestmemoryreporting(context_desc_t context_desc, struct regs r){
	u16 cs, ip;
	u16 guest_flags;
	//xc_cpu_t *xc_cpu = (xc_cpu_t *)context_desc.cpu_desc.xc_cpu;
	//xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
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
		//xc_cpu->vmcs.guest_RIP += 3;
		//xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_RIP)+3));
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
	//xc_cpu->vmcs.guest_RIP = ip;
	//xc_cpu->vmcs.guest_CS_base = cs * 16;
	//xc_cpu->vmcs.guest_CS_selector = cs;		 
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, ip);
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, (cs * 16));
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, cs);
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


//----------------------------------------------------------------------



//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
//u8 * xmhf_smpguest_arch_walk_pagetables(context_desc_t context_desc, u32 vaddr){
//		return xc_api_hpt_lvl2pagewalk(context_desc.cpu_desc.xc_cpu, vaddr);
//}

//quiesce interface to switch all guest cores into hypervisor mode
//void xmhf_smpguest_arch_quiesce(xc_cpu_t *xc_cpu){
//		xmhf_smpguest_arch_x86vmx_quiesce(xc_cpu);
//}

//endquiesce interface to resume all guest cores after a quiesce
//void xmhf_smpguest_arch_endquiesce(xc_cpu_t *xc_cpu){
//		xmhf_smpguest_arch_x86vmx_endquiesce(xc_cpu);
//}




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



//setup guest OS state for the partition
void xmhf_richguest_arch_setupguestOSstate(context_desc_t context_desc){
	xc_hypapp_arch_param_t ap;
	
	//--------------------------------------------------------------------------------------------------------------------------------
	//setup guest state
	//CR0, real-mode, PE and PG bits cleared
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & ~(CR0_PE) & ~(CR0_PG)) );
	//CR3 set to 0, does not matter
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, 0);
	ap = xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS);
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS;
	ap.param.controlregs.cr0 = ap.param.controlregs.cr0 & ~(CR0_PE) & ~(CR0_PG);
	ap.param.controlregs.cr3 = 0;
	xc_api_cpustate_set(context_desc, ap);
	
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS;
	ap.param.cpugprs.eax = 0;
	ap.param.cpugprs.ebx = 0;
	ap.param.cpugprs.ecx = 0;
	ap.param.cpugprs.edx = 0x80;
	ap.param.cpugprs.esi = 0;
	ap.param.cpugprs.edi = 0;
	ap.param.cpugprs.ebp = 0;
	ap.param.cpugprs.esp = 0;
	xc_api_cpustate_set(context_desc, ap);
							
	//RSP
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, 0);
	
	/*"movl $0x0, %%eax\r\n"
					"movl $0x0, %%ebx\r\n"
					"movl $0x0, %%ecx\r\n"
					"movl $0x80, %%edx\r\n"
					"movl $0x0, %%ebp\r\n"
					"movl $0x0, %%esi\r\n"
					"movl $0x0, %%edi\r\n"
	*/				
	
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
	ap.param.activity.rflags = ((((0 & ~((1<<3)|(1<<5)|(1<<15)) ) | (1 <<1)) | (1<<9)) & ~(1<<14));
	if(context_desc.cpu_desc.isbsp){
		ap.param.activity.rip = 0x7c00;
		ap.param.activity.activity_state = 0;	//normal activity state
	}else{
		ap.param.activity.rip = 0;
		ap.param.activity.activity_state = 3;	//wait-for-SIPI
	}
	ap.param.activity.interruptibility=0;
	xc_api_cpustate_set(context_desc, ap);

	
/*	//CS, DS, ES, FS, GS and SS segments
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, 			0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_LIMIT, 			0xFFFF 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_ACCESS_RIGHTS, 	0x93 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_SELECTOR, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_BASE, 			0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_LIMIT, 			0xFFFF 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_ACCESS_RIGHTS, 	0x93 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_SELECTOR, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_BASE, 			0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_LIMIT, 			0xFFFF 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_ACCESS_RIGHTS, 	0x93 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_SELECTOR, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_BASE, 			0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_LIMIT, 			0xFFFF 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_ACCESS_RIGHTS, 	0x93 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_SELECTOR, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_BASE, 			0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_LIMIT, 			0xFFFF 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_ACCESS_RIGHTS, 	0x93 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_SELECTOR, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_BASE, 			0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_LIMIT, 			0xFFFF 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_ACCESS_RIGHTS, 	0x93 
	//IDTR
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_BASE, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_LIMIT, 		0x3ff 
	//GDTR
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_BASE, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_LIMIT, 		0 
	//LDTR, unusable
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_BASE, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_LIMIT, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_SELECTOR, 	0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_ACCESS_RIGHTS,0x10000 
	//TR, should be usable for VMX to work, but not used by guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_BASE, 			0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_LIMIT, 			0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_SELECTOR, 		0 
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_ACCESS_RIGHTS, 	0x83 
*/

	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC;
	//CS, DS, ES, FS, GS and SS segments
	ap.param.desc.cs.selector 		 = 0  ;
	ap.param.desc.cs.base 			 = 0  ;
	ap.param.desc.cs.limit 			 = 0xFFFF  ;
	ap.param.desc.cs.access_rights 	 = 0x93  ;	
	ap.param.desc.ds.selector 		 = 0  ;
	ap.param.desc.ds.base 			 = 0  ;
	ap.param.desc.ds.limit 			 = 0xFFFF  ;
	ap.param.desc.ds.access_rights 	 = 0x93  ;	
	ap.param.desc.es.selector 		 = 0  ;
	ap.param.desc.es.base 			 = 0  ;
	ap.param.desc.es.limit 			 = 0xFFFF  ;
	ap.param.desc.es.access_rights 	 = 0x93  ;	
	ap.param.desc.fs.selector 		 = 0  ;
	ap.param.desc.fs.base 			 = 0  ;
	ap.param.desc.fs.limit 			 = 0xFFFF  ;
	ap.param.desc.fs.access_rights 	 = 0x93  ;	
	ap.param.desc.gs.selector 		 = 0  ;
	ap.param.desc.gs.base 			 = 0  ;
	ap.param.desc.gs.limit 			 = 0xFFFF  ;
	ap.param.desc.gs.access_rights 	 = 0x93  ;	
	ap.param.desc.ss.selector 		 = 0  ;
	ap.param.desc.ss.base	 		 = 0  ;
	ap.param.desc.ss.limit 			 = 0xFFFF  ;
	ap.param.desc.ss.access_rights 	 = 0x93  ;	
	//IDTR                             
	ap.param.desc.idtr.base			 = 0  ;
	ap.param.desc.idtr.limit 		 = 0x3ff  ;
	//GDTR                             
	ap.param.desc.gdtr.base			 = 0  ;
	ap.param.desc.gdtr.limit 		 = 0  ;
	//LDTR); unusable                  
	ap.param.desc.ldtr.base			 = 0  ;
	ap.param.desc.ldtr.limit 		 = 0  ;
	ap.param.desc.ldtr.selector		 = 0  ;
	ap.param.desc.ldtr.access_rights = 0x10000 ; 
	//TR); should be usable for VMX to work; not used by guest
	ap.param.desc.tr.base 			 = 0  ;	
	ap.param.desc.tr.limit 			 = 0  ;	
	ap.param.desc.tr.selector 		 = 0  ;	
	ap.param.desc.tr.access_rights 	 = 0x83  ; 	
	xc_api_cpustate_set(context_desc, ap);

}
