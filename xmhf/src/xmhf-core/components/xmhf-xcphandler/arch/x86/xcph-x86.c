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
 * EMHF exception handler component interface
 * x86 arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//---function to obtain the vcpu of the currently executing core----------------
//XXX: TODO, move this into baseplatform as backend
//note: this always returns a valid VCPU pointer
static VCPU *_svm_getvcpu(void){
  
  int i;
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;
  
  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  eax &= (u32)0xFFFFF000UL;
  lapic_reg = (u32 *)((u32)eax+ (u32)LAPIC_ID);
  lapic_id = *lapic_reg;
  //printf("\n%s: lapic base=0x%08x, id reg=0x%08x", __FUNCTION__, eax, lapic_id);
  lapic_id = lapic_id >> 24;
  //printf("\n%s: lapic_id of core=0x%02x", __FUNCTION__, lapic_id);
  
  for(i=0; i < (int)g_midtable_numentries; i++){
    if(g_midtable[i].cpu_lapic_id == lapic_id)
        return( (VCPU *)g_midtable[i].vcpu_vaddr_ptr );
  }

  printf("\n%s: fatal, unable to retrieve vcpu for id=0x%02x", __FUNCTION__, lapic_id);
  HALT(); return NULL; // will never return presently 
  
}

//---function to obtain the vcpu of the currently executing core----------------
//XXX: move this into baseplatform as backend
//note: this always returns a valid VCPU pointer
static VCPU *_vmx_getvcpu(void){
  int i;
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;
  
  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  eax &= (u32)0xFFFFF000UL;
  lapic_reg = (u32 *)((u32)eax+ (u32)LAPIC_ID);
  lapic_id = *lapic_reg;
  //printf("\n%s: lapic base=0x%08x, id reg=0x%08x", __FUNCTION__, eax, lapic_id);
  lapic_id = lapic_id >> 24;
  //printf("\n%s: lapic_id of core=0x%02x", __FUNCTION__, lapic_id);
  
  for(i=0; i < (int)g_midtable_numentries; i++){
    if(g_midtable[i].cpu_lapic_id == lapic_id)
        return( (VCPU *)g_midtable[i].vcpu_vaddr_ptr );
  }

  printf("\n%s: fatal, unable to retrieve vcpu for id=0x%02x", __FUNCTION__, lapic_id);
  HALT();
  return NULL; // currently unreachable 
  
}


//initialize EMHF core exception handlers
void emhf_xcphandler_arch_initialize(void){
	u32 *pexceptionstubs;
	u32 i;

	printf("\n%s: setting up runtime IDT...", __FUNCTION__);
	
	//pexceptionstubs=(u32 *)&emhf_xcphandler_exceptionstubs;
	pexceptionstubs=(u32 *)&emhf_xcphandler_exceptionstubs;
	
	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		idtentry_t *idtentry=(idtentry_t *)((u32)emhf_xcphandler_arch_get_idt_start()+ (i*8));
		idtentry->isrLow= (u16)pexceptionstubs[i];
		idtentry->isrHigh= (u16) ( (u32)pexceptionstubs[i] >> 16 );
		idtentry->isrSelector = __CS;
		idtentry->count=0x0;
		idtentry->type=0x8E;	//32-bit interrupt gate
								//present=1, DPL=00b, system=0, type=1110b
	}
	
	printf("\n%s: IDT setup done.", __FUNCTION__);
}


//get IDT start address
u8 * emhf_xcphandler_arch_get_idt_start(void){
	return (u8 *)&emhf_xcphandler_idt_start;
}


//EMHF exception handler hub
void emhf_xcphandler_arch_hub(u32 vector, struct regs *r){
	u32 cpu_vendor = get_cpu_vendor_or_die();	//determine CPU vendor
	VCPU *vcpu;
	
	if(cpu_vendor == CPU_VENDOR_AMD){
		vcpu=_svm_getvcpu();
	}else{	//CPU_VENDOR_INTEL
	    vcpu=_vmx_getvcpu();
	}	
	
	switch(vector){
			case CPU_EXCEPTION_NMI:
				emhf_smpguest_arch_x86_eventhandler_nmiexception(vcpu, r);
				break;

			default:{
				u32 exception_cs, exception_eip, exception_eflags;

				if(vector == CPU_EXCEPTION_DF ||
					vector == CPU_EXCEPTION_TS ||
					vector == CPU_EXCEPTION_NP ||
					vector == CPU_EXCEPTION_SS ||
					vector == CPU_EXCEPTION_GP ||
					vector == CPU_EXCEPTION_PF ||
					vector == CPU_EXCEPTION_AC){
					r->esp += sizeof(uint32_t);	//skip error code on stack if applicable
				}
				
				exception_eip = *(uint32_t *)(r->esp+0);
				exception_cs = *(uint32_t *)(r->esp+sizeof(uint32_t));
				exception_eflags = *(uint32_t *)(r->esp+(2*sizeof(uint32_t)));

				printf("\n[%02x]: unhandled exception, halting!", vcpu->id);
				printf("\n[%02x]: state dump follows...", vcpu->id);
				//things to dump
				printf("\n[%02x] CS:EIP 0x%04x:0x%08x with EFLAGS=0x%08x", vcpu->id,
					(u16)exception_cs, exception_eip, exception_eflags);
				printf("\n[%02x]: VCPU at 0x%08x", vcpu->id, (u32)vcpu, vcpu->id);
				printf("\n[%02x] EAX=0x%08x EBX=0x%08x ECX=0x%08x EDX=0x%08x", vcpu->id,
						r->eax, r->ebx, r->ecx, r->edx);
				printf("\n[%02x] ESI=0x%08x EDI=0x%08x EBP=0x%08x ESP=0x%08x", vcpu->id,
						r->esi, r->edi, r->ebp, r->esp);
				printf("\n[%02x] CS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x", vcpu->id,
					(u16)read_segreg_cs(), (u16)read_segreg_ds(),
					(u16)read_segreg_es(), (u16)read_segreg_ss());
				printf("\n[%02x] FS=0x%04x, GS=0x%04x", vcpu->id,
					(u16)read_segreg_fs(), (u16)read_segreg_gs());
				printf("\n[%02x] TR=0x%04x", vcpu->id, (u16)read_tr_sel());
				
				//do a stack dump in the hopes of getting more info.
				{
					//vcpu->esp is the TOS
					uint32_t i;
					//uint32_t stack_start = (r->esp+(3*sizeof(uint32_t)));
					uint32_t stack_start = r->esp;
					printf("\n[%02x]-----stack dump-----", vcpu->id);
					for(i=stack_start; i < vcpu->esp; i+=sizeof(uint32_t)){
						printf("\n[%02x]  Stack(0x%08x) -> 0x%08x", vcpu->id, i, *(uint32_t *)i);
					}
					printf("\n[%02x]-----end------------", vcpu->id);
				}
				HALT();
			}
	}
}
