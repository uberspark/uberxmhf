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

// islayer.c
// author: amit vasudevan (amitvasudevan@acm.org) 
#include <target.h>


//---globals and externs--------------------------------------------------------
extern u32 __runtime_v86_pagedir[];
extern u32 __runtime_v86_idt[]; 
extern u32 __runtime_v86_gdt[], __runtime_v86_ldt[], __runtime_v86_tss[];

VCPU *getvcpu(void);

u8 vmx_iobitmap_buffer[(2 * PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));

u8 vmx_msr_area_host[(2 * PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));
u8 vmx_msr_area_guest[(2 * PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));


u8 vmx_ept_pml4_table[PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));
u8 vmx_ept_pdp_table[PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));
u8 vmx_ept_pd_tables[PAGE_SIZE_4K*4] __attribute__(( section(".vtdata" ) ));	
u8 vmx_ept_p_tables[PAGE_SIZE_4K*2048] __attribute__(( section(".vtdata" ) )); //4GB	



u32 isl_guesthastr=0;
u32 isl_guest_TR_base   = 0;
u32 isl_guest_TR_access_rights   = 0;
u32 isl_guest_TR_limit   = 0;
u16 isl_guest_TR_selector=0;
u32 isl_guest_LDTR_base   = 0;
u32 isl_guest_LDTR_access_rights   = 0;
u32 isl_guest_LDTR_limit   = 0;
u16 isl_guest_LDTR_selector=0;
u32 limbo_rsp=0;

u16 guest_limbo_cs=0;
u32 guest_limbo_eip=0;

u32 guestcr3val_when_cr0_pg_off=0; //contains CR3 values manipulated by guest when CR0.PG=0



//critical MSRs that need to be saved/restored across guest VM switches
static const u32 vmx_msr_area_msrs[] = {
	MSR_EFER, MSR_K6_STAR
};

const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));


struct _vmcsrofields_encodings	{
 unsigned int  encoding; 
 unsigned int  fieldoffset; 
} __attribute__((packed)) vmcsrofields_encodings[] = {
	{ 0x4400, offsetof(struct vmcsfields, info_vminstr_error) }, 
	{ 0x4402, offsetof(struct vmcsfields, info_vmexit_reason) },
	{ 0x4404, offsetof(struct vmcsfields, info_vmexit_interrupt_information) },
	{ 0x4406, offsetof(struct vmcsfields, info_vmexit_interrupt_error_code) },
	{ 0x4408, offsetof(struct vmcsfields, info_IDT_vectoring_information) },
	{ 0x440A, offsetof(struct vmcsfields, info_IDT_vectoring_error_code) },
	{ 0x440C, offsetof(struct vmcsfields, info_vmexit_instruction_length) },
	{ 0x440E, offsetof(struct vmcsfields, info_vmx_instruction_information) },
	{ 0x6400, offsetof(struct vmcsfields, info_exit_qualification) },
	{ 0x6402, offsetof(struct vmcsfields, info_IO_RCX) },
	{ 0x6404, offsetof(struct vmcsfields, info_IO_RSI) },
	{ 0x6406, offsetof(struct vmcsfields, info_IO_RDI) },
	{ 0x6408, offsetof(struct vmcsfields, info_IO_RIP) },
#if defined(__NESTED_PAGING__)
	{ 0x2400, offsetof(struct vmcsfields, guest_paddr_full) },
	{ 0x2401, offsetof(struct vmcsfields, guest_paddr_high) },
#endif
	{ 0x640A, offsetof(struct vmcsfields, info_guest_linear_address) } 
};

const unsigned int vmcsrofields_encodings_count = sizeof( vmcsrofields_encodings ) / sizeof( struct _vmcsrofields_encodings );

struct _vmcsrwfields_encodings	{
 unsigned int  encoding; 
 unsigned int  fieldoffset; 
} __attribute__((packed)) vmcsrwfields_encodings[] = {
	// Control fields
#if defined(__NESTED_PAGING__)
  //16-bit control field
  { 0x0000, offsetof(struct vmcsfields, control_vpid) },
#endif
	// Natural 32-bit Control fields
	{ 0x4000, offsetof(struct vmcsfields, control_VMX_pin_based) },
	{ 0x4002, offsetof(struct vmcsfields, control_VMX_cpu_based) },
#if defined(__NESTED_PAGING__)
	{ 0x401E, offsetof(struct vmcsfields, control_VMX_seccpu_based) },
#endif
	{ 0x4004, offsetof(struct vmcsfields, control_exception_bitmap) },
	{ 0x4006, offsetof(struct vmcsfields, control_pagefault_errorcode_mask) },
	{ 0x4008, offsetof(struct vmcsfields, control_pagefault_errorcode_match) },
	{ 0x400A, offsetof(struct vmcsfields, control_CR3_target_count) },
	{ 0x400C, offsetof(struct vmcsfields, control_VM_exit_controls) },
	{ 0x400E, offsetof(struct vmcsfields, control_VM_exit_MSR_store_count) },
	{ 0x4010, offsetof(struct vmcsfields, control_VM_exit_MSR_load_count) },
	{ 0x4012, offsetof(struct vmcsfields, control_VM_entry_controls) },
	{ 0x4014, offsetof(struct vmcsfields, control_VM_entry_MSR_load_count) },
	{ 0x4016, offsetof(struct vmcsfields, control_VM_entry_interruption_information) },
	{ 0x4018, offsetof(struct vmcsfields, control_VM_entry_exception_errorcode) },
	{ 0x401A, offsetof(struct vmcsfields, control_VM_entry_instruction_length) },
	{ 0x401C, offsetof(struct vmcsfields, control_Task_PRivilege_Threshold) },
	// Natural 64-bit Control fields
	{ 0x6000, offsetof(struct vmcsfields, control_CR0_mask) },
	{ 0x6002, offsetof(struct vmcsfields, control_CR4_mask) }, 
	{ 0x6004, offsetof(struct vmcsfields, control_CR0_shadow) },
	{ 0x6006, offsetof(struct vmcsfields, control_CR4_shadow) },
	{ 0x6008, offsetof(struct vmcsfields, control_CR3_target0) },
	{ 0x600A, offsetof(struct vmcsfields, control_CR3_target1) },
	{ 0x600C, offsetof(struct vmcsfields, control_CR3_target2) },
	{ 0x600E, offsetof(struct vmcsfields, control_CR3_target3) },
	// Full 64-bit Control fields
	{ 0x2000, offsetof(struct vmcsfields, control_IO_BitmapA_address_full) },
	{ 0x2001, offsetof(struct vmcsfields, control_IO_BitmapA_address_high) },
	{ 0x2002, offsetof(struct vmcsfields, control_IO_BitmapB_address_full) },
	{ 0x2003, offsetof(struct vmcsfields, control_IO_BitmapB_address_high) },
	//{ 0x2004, offsetof(struct vmcsfields, control_MSR_Bitmaps_address_full) },
	//{ 0x2005, offsetof(struct vmcsfields, control_MSR_Bitmaps_address_high) }, 
	{ 0x2006, offsetof(struct vmcsfields, control_VM_exit_MSR_store_address_full) },
	{ 0x2007, offsetof(struct vmcsfields, control_VM_exit_MSR_store_address_high) },
	{ 0x2008, offsetof(struct vmcsfields, control_VM_exit_MSR_load_address_full) },
	{ 0x2009, offsetof(struct vmcsfields, control_VM_exit_MSR_load_address_high) },
	{ 0x200A, offsetof(struct vmcsfields, control_VM_entry_MSR_load_address_full) },
	{ 0x200B, offsetof(struct vmcsfields, control_VM_entry_MSR_load_address_high) },
	{ 0x200C, offsetof(struct vmcsfields, control_Executive_VMCS_pointer_full) },
	{ 0x200D, offsetof(struct vmcsfields, control_Executive_VMCS_pointer_high) },
	{ 0x2010, offsetof(struct vmcsfields, control_TSC_offset_full) },
	{ 0x2011, offsetof(struct vmcsfields, control_TSC_offset_high) },
	//{ 0x2012, offsetof(struct vmcsfields, control_virtual_APIC_page_address_full) }, 
	//{ 0x2013, offsetof(struct vmcsfields, control_virtual_APIC_page_address_high) },
#if defined(__NESTED_PAGING__)
	{ 0x201A, offsetof(struct vmcsfields, control_EPT_pointer_full) },
	{ 0x201B, offsetof(struct vmcsfields, control_EPT_pointer_high) },
#endif
	// Host-State fields
	// Natural 64-bit Host-State fields
	{ 0x6C00, offsetof(struct vmcsfields, host_CR0) },
	{ 0x6C02, offsetof(struct vmcsfields, host_CR3) },
	{ 0x6C04, offsetof(struct vmcsfields, host_CR4) },
	{ 0x6C06, offsetof(struct vmcsfields, host_FS_base) },
	{ 0x6C08, offsetof(struct vmcsfields, host_GS_base) },
	{ 0x6C0A, offsetof(struct vmcsfields, host_TR_base) },
	{ 0x6C0C, offsetof(struct vmcsfields, host_GDTR_base) },
	{ 0x6C0E, offsetof(struct vmcsfields, host_IDTR_base) },
	{ 0x6C10, offsetof(struct vmcsfields, host_SYSENTER_ESP) },
	{ 0x6C12, offsetof(struct vmcsfields, host_SYSENTER_EIP) },
	{ 0x6C14, offsetof(struct vmcsfields, host_RSP) },
	{ 0x6C16, offsetof(struct vmcsfields, host_RIP) },
	// Natural 32-bit Host-State fields
	{ 0x4C00, offsetof(struct vmcsfields, host_SYSENTER_CS) },
	// Natural 16-bit Host-State fields
	{ 0x0C00, offsetof(struct vmcsfields, host_ES_selector) },
	{ 0x0C02, offsetof(struct vmcsfields, host_CS_selector) },
	{ 0x0C04, offsetof(struct vmcsfields, host_SS_selector) },
	{ 0x0C06, offsetof(struct vmcsfields, host_DS_selector) },
	{ 0x0C08, offsetof(struct vmcsfields, host_FS_selector) },
	{ 0x0C0A, offsetof(struct vmcsfields, host_GS_selector) },
	{ 0x0C0C, offsetof(struct vmcsfields, host_TR_selector) },
	// Guest-State fields
	// Natural 64-bit Guest-State fields
	{ 0x6800, offsetof(struct vmcsfields, guest_CR0) },
	{ 0x6802, offsetof(struct vmcsfields, guest_CR3) },
	{ 0x6804, offsetof(struct vmcsfields, guest_CR4) },
	{ 0x6806, offsetof(struct vmcsfields, guest_ES_base) },
	{ 0x6808, offsetof(struct vmcsfields, guest_CS_base) },
	{ 0x680A, offsetof(struct vmcsfields, guest_SS_base) },
	{ 0x680C, offsetof(struct vmcsfields, guest_DS_base) },
	{ 0x680E, offsetof(struct vmcsfields, guest_FS_base) },
	{ 0x6810, offsetof(struct vmcsfields, guest_GS_base) },
	{ 0x6812, offsetof(struct vmcsfields, guest_LDTR_base) },
	{ 0x6814, offsetof(struct vmcsfields, guest_TR_base) },
	{ 0x6816, offsetof(struct vmcsfields, guest_GDTR_base) },
	{ 0x6818, offsetof(struct vmcsfields, guest_IDTR_base) },
	{ 0x681A, offsetof(struct vmcsfields, guest_DR7) },
	{ 0x681C, offsetof(struct vmcsfields, guest_RSP) },
	{ 0x681E, offsetof(struct vmcsfields, guest_RIP) },
	{ 0x6820, offsetof(struct vmcsfields, guest_RFLAGS) },
	{ 0x6822, offsetof(struct vmcsfields, guest_pending_debug_x) },
	{ 0x6824, offsetof(struct vmcsfields, guest_SYSENTER_ESP) },
	{ 0x6826, offsetof(struct vmcsfields, guest_SYSENTER_EIP) },
#if defined(__NESTED_PAGING__)
	{ 0x280A, offsetof(struct vmcsfields, guest_PDPTE0_full) },
	{ 0x280B, offsetof(struct vmcsfields, guest_PDPTE0_high) },
	{ 0x280C, offsetof(struct vmcsfields, guest_PDPTE1_full) },
	{ 0x280D, offsetof(struct vmcsfields, guest_PDPTE1_high) },
	{ 0x280E, offsetof(struct vmcsfields, guest_PDPTE2_full) },
	{ 0x280F, offsetof(struct vmcsfields, guest_PDPTE2_high) },
	{ 0x2810, offsetof(struct vmcsfields, guest_PDPTE3_full) },
	{ 0x2811, offsetof(struct vmcsfields, guest_PDPTE3_high) },
#endif
	// Natural 32-bit Guest-State fields
	{ 0x4800, offsetof(struct vmcsfields, guest_ES_limit) },
	{ 0x4802, offsetof(struct vmcsfields, guest_CS_limit) },
	{ 0x4804, offsetof(struct vmcsfields, guest_SS_limit) },
	{ 0x4806, offsetof(struct vmcsfields, guest_DS_limit) },
	{ 0x4808, offsetof(struct vmcsfields, guest_FS_limit) },
	{ 0x480A, offsetof(struct vmcsfields, guest_GS_limit) },
	{ 0x480C, offsetof(struct vmcsfields, guest_LDTR_limit) },
	{ 0x480E, offsetof(struct vmcsfields, guest_TR_limit) },
	{ 0x4810, offsetof(struct vmcsfields, guest_GDTR_limit) },
	{ 0x4812, offsetof(struct vmcsfields, guest_IDTR_limit) },
	{ 0x4814, offsetof(struct vmcsfields, guest_ES_access_rights) },
	{ 0x4816, offsetof(struct vmcsfields, guest_CS_access_rights) },
	{ 0x4818, offsetof(struct vmcsfields, guest_SS_access_rights) },
	{ 0x481A, offsetof(struct vmcsfields, guest_DS_access_rights) },
	{ 0x481C, offsetof(struct vmcsfields, guest_FS_access_rights) },
	{ 0x481E, offsetof(struct vmcsfields, guest_GS_access_rights) },
	{ 0x4820, offsetof(struct vmcsfields, guest_LDTR_access_rights) },
	{ 0x4822, offsetof(struct vmcsfields, guest_TR_access_rights) },
	{ 0x4824, offsetof(struct vmcsfields, guest_interruptibility) },
	{ 0x4826, offsetof(struct vmcsfields, guest_activity_state) },
	{ 0x4828, offsetof(struct vmcsfields, guest_SMBASE) },
	{ 0x482A, offsetof(struct vmcsfields, guest_SYSENTER_CS) },
	// Natural 16-bit Guest-State fields
	{ 0x0800, offsetof(struct vmcsfields, guest_ES_selector) },
	{ 0x0802, offsetof(struct vmcsfields, guest_CS_selector) },
	{ 0x0804, offsetof(struct vmcsfields, guest_SS_selector) },
	{ 0x0806, offsetof(struct vmcsfields, guest_DS_selector) },
	{ 0x0808, offsetof(struct vmcsfields, guest_FS_selector) },
	{ 0x080A, offsetof(struct vmcsfields, guest_GS_selector) },
	{ 0x080C, offsetof(struct vmcsfields, guest_LDTR_selector) },
	{ 0x080E, offsetof(struct vmcsfields, guest_TR_selector) },
	// Full 64-bit Guest-State fields
	{ 0x2800, offsetof(struct vmcsfields, guest_VMCS_link_pointer_full) },
	{ 0x2801, offsetof(struct vmcsfields, guest_VMCS_link_pointer_high) },
	{ 0x2802, offsetof(struct vmcsfields, guest_IA32_DEBUGCTL_full) },
	{ 0x2803, offsetof(struct vmcsfields, guest_IA32_DEBUGCTL_high) } 
};

const unsigned int vmcsrwfields_encodings_count = sizeof( vmcsrwfields_encodings ) / sizeof( struct _vmcsrwfields_encodings );


//---VMX decode assist----------------------------------------------------------
//map a CPU register index into appropriate VCPU *vcpu or struct regs *r field 
//and return the address of the field
u32 * vmx_decode_reg(u32 gpr, VCPU *vcpu, struct regs *r){
  ASSERT ( ((int)gpr >=0) && ((int)gpr <= 7) );
  
  switch(gpr){
    case 0: return ( (u32 *)&r->eax );
    case 1: return ( (u32 *)&r->ecx );
    case 2: return ( (u32 *)&r->edx );
    case 3: return ( (u32 *)&r->ebx );
    case 4: return ( (u32 *)&vcpu->vmcs.guest_RSP);
    case 5: return ( (u32 *)&r->ebp );
    case 6: return ( (u32 *)&r->esi );
    case 7: return ( (u32 *)&r->edi );
  }
}


//---putVMCS--------------------------------------------------------------------
// routine takes vcpu vmcsfields and stores it in the CPU VMCS 
void putVMCS(VCPU *vcpu){
    unsigned int i;
    for(i=0; i < vmcsrwfields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)vmcsrwfields_encodings[i].fieldoffset);
      u32 fieldvalue = *field;
      //printf("\nvmwrite: enc=0x%08x, value=0x%08x", vmcsrwfields_encodings[i].encoding, fieldvalue);
      if(!__vmx_vmwrite(vmcsrwfields_encodings[i].encoding, fieldvalue)){
        printf("\nCPU(0x%02x): VMWRITE failed. HALT!", vcpu->id);
        HALT();
      }
    }
}

//---getVMCS--------------------------------------------------------------------
// routine takes CPU VMCS and stores it in vcpu vmcsfields  
void getVMCS(VCPU *vcpu){
  unsigned int i;
  for(i=0; i < vmcsrwfields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)vmcsrwfields_encodings[i].fieldoffset);
      __vmx_vmread(vmcsrwfields_encodings[i].encoding, field);
  }  
  for(i=0; i < vmcsrofields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)vmcsrofields_encodings[i].fieldoffset);
      __vmx_vmread(vmcsrofields_encodings[i].encoding, field);
  }  
}

//--debug: dumpVMCS dumps VMCS contents-----------------------------------------
void dumpVMCS(VCPU *vcpu){
  		printf("\nGuest State follows:");
		printf("\nguest_CS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_CS_selector);
		printf("\nguest_DS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_DS_selector);
		printf("\nguest_ES_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_ES_selector);
		printf("\nguest_FS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_FS_selector);
		printf("\nguest_GS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_GS_selector);
		printf("\nguest_SS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_SS_selector);
		printf("\nguest_TR_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_TR_selector);
		printf("\nguest_LDTR_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_LDTR_selector);
		printf("\nguest_CS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_CS_access_rights);
		printf("\nguest_DS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_DS_access_rights);
		printf("\nguest_ES_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_ES_access_rights);
		printf("\nguest_FS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_FS_access_rights);
		printf("\nguest_GS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_GS_access_rights);
		printf("\nguest_SS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_SS_access_rights);
		printf("\nguest_TR_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_TR_access_rights);
		printf("\nguest_LDTR_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_LDTR_access_rights);

		printf("\nguest_CS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_CS_base, (unsigned short)vcpu->vmcs.guest_CS_limit);
		printf("\nguest_DS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_DS_base, (unsigned short)vcpu->vmcs.guest_DS_limit);
		printf("\nguest_ES_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_ES_base, (unsigned short)vcpu->vmcs.guest_ES_limit);
		printf("\nguest_FS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_FS_base, (unsigned short)vcpu->vmcs.guest_FS_limit);
		printf("\nguest_GS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_GS_base, (unsigned short)vcpu->vmcs.guest_GS_limit);
		printf("\nguest_SS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_SS_base, (unsigned short)vcpu->vmcs.guest_SS_limit);
		printf("\nguest_GDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)vcpu->vmcs.guest_GDTR_base, (unsigned short)vcpu->vmcs.guest_GDTR_limit);		
		printf("\nguest_IDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)vcpu->vmcs.guest_IDTR_base, (unsigned short)vcpu->vmcs.guest_IDTR_limit);		
		printf("\nguest_TR_base/limit=0x%08lx/0x%04x",
			(unsigned long)vcpu->vmcs.guest_TR_base, (unsigned short)vcpu->vmcs.guest_TR_limit);		
		printf("\nguest_LDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)vcpu->vmcs.guest_LDTR_base, (unsigned short)vcpu->vmcs.guest_LDTR_limit);		

		printf("\nguest_CR0=0x%08lx, guest_CR4=0x%08lx, guest_CR3=0x%08lx",
			(unsigned long)vcpu->vmcs.guest_CR0, (unsigned long)vcpu->vmcs.guest_CR4,
			(unsigned long)vcpu->vmcs.guest_CR3);
		printf("\nguest_RSP=0x%08lx", (unsigned long)vcpu->vmcs.guest_RSP);
		printf("\nguest_RIP=0x%08lx", (unsigned long)vcpu->vmcs.guest_RIP);
		printf("\nguest_RFLAGS=0x%08lx", (unsigned long)vcpu->vmcs.guest_RFLAGS);
}

//---generic exception handler--------------------------------------------------
void XtRtmExceptionHandler(u32 vector, struct regs *r){
	VCPU *vcpu = getvcpu();
  INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *noecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *)((u32)r->esp + (u32)0x0C);
  INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *ecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *)((u32)r->esp + (u32)0x0C);

  printf("\nCPU(0x%02x): XtRtmExceptionHandler: Exception=0x%08X", vcpu->id, vector);
  printf("\nCPU(0x%02x): ESP=0x%08x", vcpu->id, r->esp);
  //if(vector == 0x2){
  //  processNMI(vcpu, (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr, r);
  //  return;
  //}	
  HALT();
}

extern u32 x_gdt_start[], x_idt_start[], __runtimetss[];
extern void __islayer_callback(void);

//---isl_prepareVMCS - change VMCS depending upon the guest state---------------
//this is necessary on VT as we need to have a V86 monitor to tackle real-mode
//code execution. note: while EPTs allow real-mode code to execute with 
//physical memory protection, unless we have the unrestricted guest caps 
//we still need the V86 monitor. as of this writing uguestcaps is still
//unavailable on intel platforms.
//inputs: currentstate = current state of guest, nextstate= desired state
//returns the new currentstate
u32 isl_prepareVMCS(VCPU *vcpu, struct regs *r, u32 currentstate, u32 nextstate){
	u32 lodword, hidword;
	
  if(currentstate == GSTATE_DEAD){
		ASSERT((nextstate == GSTATE_REALMODE));

			//setup host state
			vcpu->vmcs.host_CR0 = read_cr0();
			vcpu->vmcs.host_CR4 = read_cr4();
			vcpu->vmcs.host_CR3 = read_cr3();
			vcpu->vmcs.host_CS_selector = read_segreg_cs();
			vcpu->vmcs.host_DS_selector = read_segreg_ds();
			vcpu->vmcs.host_ES_selector = read_segreg_es();
			vcpu->vmcs.host_FS_selector = read_segreg_fs();
			vcpu->vmcs.host_GS_selector = read_segreg_gs();
			vcpu->vmcs.host_SS_selector = read_segreg_ss();
			vcpu->vmcs.host_TR_selector = read_tr_sel();
			vcpu->vmcs.host_GDTR_base = (u64)(u32)x_gdt_start;
			vcpu->vmcs.host_IDTR_base = (u64)(u32)x_idt_start;
			vcpu->vmcs.host_TR_base = (u64)(u32)__runtimetss;
			vcpu->vmcs.host_RIP = (u64)(u32)__islayer_callback;
			vcpu->vmcs.host_RSP = (u64)vcpu->esp;
			rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_CS = lodword;
      rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_ESP = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_EIP = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
      vcpu->vmcs.host_FS_base = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
      vcpu->vmcs.host_GS_base = (u64) (((u64)hidword << 32) | (u64)lodword);

      //setup VMX controls
  			vcpu->vmcs.control_VMX_pin_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR];
        vcpu->vmcs.control_VMX_cpu_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR];
  			vcpu->vmcs.control_VM_exit_controls = vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR];
  			vcpu->vmcs.control_VM_entry_controls = vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR];
  			vcpu->vmcs.control_CR0_mask = vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];	
      
        //HLT instruction intercept, our V86 monitor signals end-of-real-mode using this
        vcpu->vmcs.control_VMX_cpu_based |= (1<<7);	
  	 		vcpu->vmcs.control_CR0_shadow = V86M_CR0_INITIALVALUE; //real-mode, no-paging

  			//IO bitmap support
  			memset( (void *)vmx_iobitmap_buffer, 0, (PAGE_SIZE_4K * 2));
				vcpu->vmcs.control_IO_BitmapA_address_full = (u32)__hva2spa__((u32)vmx_iobitmap_buffer);
				vcpu->vmcs.control_IO_BitmapA_address_high = 0;
				vcpu->vmcs.control_IO_BitmapB_address_full = (u32)__hva2spa__( ((u32)vmx_iobitmap_buffer + PAGE_SIZE_4K) );
				vcpu->vmcs.control_IO_BitmapB_address_high = 0;
				vcpu->vmcs.control_VMX_cpu_based |= (1 << 25); //enable use IO Bitmaps
				//islayer_set_ioport_intercept(ACPI_CONTROLREG_PORT);
				//islayer_set_ioport_intercept(ACPI_STATUSREG_PORT);

				//Critical MSR load/store
				{
					u32 i;
  				msr_entry_t *hmsr = (msr_entry_t *)vmx_msr_area_host;
					msr_entry_t *gmsr = (msr_entry_t *)vmx_msr_area_guest;

					//store initial values of the MSRs
					for(i=0; i < vmx_msr_area_msrs_count; i++){
						u32 msr, eax, edx;
	          msr = vmx_msr_area_msrs[i];						
						rdmsr(msr, &eax, &edx);
						hmsr[i].index = gmsr[i].index = msr;
						hmsr[i].data = gmsr[i].data = ((u64)edx << 32) | (u64)eax;
					}
					
					//host MSR load on exit, we store it ourselves before entry
					vcpu->vmcs.control_VM_exit_MSR_load_address_full=(u32)__hva2spa__((u32)vmx_msr_area_host);
					vcpu->vmcs.control_VM_exit_MSR_load_address_high=0;
					vcpu->vmcs.control_VM_exit_MSR_load_count= vmx_msr_area_msrs_count;
					
					//guest MSR load on entry, store on exit
					vcpu->vmcs.control_VM_entry_MSR_load_address_full=(u32)__hva2spa__((u32)vmx_msr_area_guest);
					vcpu->vmcs.control_VM_entry_MSR_load_address_high=0;
					vcpu->vmcs.control_VM_entry_MSR_load_count=vmx_msr_area_msrs_count;
				  vcpu->vmcs.control_VM_exit_MSR_store_address_full=(u32)__hva2spa__((u32)vmx_msr_area_guest);
					vcpu->vmcs.control_VM_exit_MSR_store_address_high=0;
					vcpu->vmcs.control_VM_exit_MSR_store_count=vmx_msr_area_msrs_count;
				}
				

				vcpu->vmcs.control_pagefault_errorcode_mask  = 0x00000000;	//dont be concerned with 
				vcpu->vmcs.control_pagefault_errorcode_match = 0x00000000; //guest page-faults
				vcpu->vmcs.control_exception_bitmap = 0;
				vcpu->vmcs.control_CR3_target_count = 0;
				vcpu->vmcs.control_CR4_mask = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR] | CR4_PAE; //we want to intercept access to these bits 
	 			vcpu->vmcs.control_CR4_shadow = CR4_VMXE; //let guest know we have VMX enabled
      
      //setup guest state
			v86monitor_initializeguest(vcpu);

#ifdef __NESTED_PAGING__
		  {
        //setup EPT
        vmx_gathermemorytypes(vcpu);
        vmx_setupEPT(vcpu);
        vcpu->vmcs.control_VMX_seccpu_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR];
  			vcpu->vmcs.control_VMX_cpu_based |= (1 << 31); //activate secondary processor controls
  			vcpu->vmcs.control_VMX_seccpu_based |= (1 << 1); //enable EPT
  			vcpu->vmcs.control_VMX_seccpu_based |= (1 << 5); //enable VPID
  			vcpu->vmcs.control_vpid = 1; //VPID=0 is reserved for hypervisor
  			vcpu->vmcs.control_EPT_pointer_high = 0;
  			vcpu->vmcs.control_EPT_pointer_full = __hva2spa__((u32)vmx_ept_pml4_table) | 0x1E; //page walk of 4 and WB memory
 				vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
				vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting

      }
#else
      //no hardware paging, so we need to intercept CR3 accesses
			vcpu->vmcs.control_VMX_cpu_based |= (1 << 15); //enable CR3 load exiting
			vcpu->vmcs.control_VMX_cpu_based |= (1 << 16); //enable CR3 store exiting
#endif			

      #if defined (__NESTED_PAGING__)
			__vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
      #endif

      
		return(nextstate);
		// END if(currentstate == GSTATE_DEAD)
	}else if(currentstate == GSTATE_REALMODE){
		ASSERT( (nextstate == GSTATE_PROTECTEDMODE) ||
			(nextstate == (GSTATE_PROTECTEDMODE | GSTATE_PROTECTEDMODE_PG) )
			);
	  ASSERT( r != NULL );
	  
		//guest has loaded a GDT, might have loaded IDT and set PG, but before
		//the GDT can take effect, the guest usually performs a long jump or
		//a retf. So, we have to plug in temporary CS and SS selectors
		//defined with 64K limit until the long jump or retf is performed. 
		//We set our CS and SS selectors above the limit already loaded by
		//the guest. This way we can be sure that our selector values do not
		//collide with guest selector values and we will always get a general
		//protection fault (#GP, 0x0D) when the guest tries to do a 
		//far jump or retf
		
		//setup VMCS controls
		vcpu->vmcs.control_VMX_cpu_based &= ~(1<<7);	// clear HLT-exiting
		vcpu->vmcs.control_exception_bitmap |= (1UL << 13); //set INT 13 (#GP fault)
		
		//setup guest portion
		{
			//setup GDT
			{
					u64 *gdt;
					u64 desc;
					memset((void *)__limbo_gdt, LIMBO_GDT_SIZE, 0);
					gdt = (u64 *)(u32)__limbo_gdt;
					ASSERT( (v86monitor_guest_gdt_base != 0) && 
									(v86monitor_guest_gdt_limit != 0) );
					vcpu->vmcs.guest_CS_selector = (v86monitor_guest_gdt_limit + 1) + 0x08;								
					vcpu->vmcs.guest_SS_selector = (v86monitor_guest_gdt_limit + 1) + 0x10;
					vcpu->vmcs.guest_TR_selector = (v86monitor_guest_gdt_limit + 1) + 0x18;
					//printf("\nguest gdt: base=0x%08lx, size=0x%04x",
					//	(unsigned long)v86monitor_guest_gdt_base, 
					//	(unsigned short)v86monitor_guest_gdt_limit);
					//printf("\nlimbo selectors: CS=0x%04x, SS=0x%04x, TR=0x%04x",
					//	(unsigned short)guest_CS_selector, 
					//	(unsigned short)guest_SS_selector,
					//	(unsigned short)guest_TR_selector);

					//printf("\nguest segment registers: CS=0x%04x, SS=0x%04x",
					//	(unsigned short)v86monitor_guest_reg_cs, 
					//	(unsigned short)v86monitor_guest_reg_ss);

					desc = (u64)(u32)(v86monitor_guest_reg_cs * 16);
					desc = ((desc & 0xFF000000)<<32)|((desc & 0x00FFFFFF)<<16);
					desc |= 0xFFFF | ( 0x009BULL << 40);
					gdt[vcpu->vmcs.guest_CS_selector >> 3] = desc;

					desc = (u64)(u32)(v86monitor_guest_reg_ss * 16);
					desc = ((desc & 0xFF000000)<<32)|((desc & 0x00FFFFFF)<<16);
					desc |= 0xFFFF | ( 0x0093ULL << 40);
					gdt[vcpu->vmcs.guest_SS_selector >> 3] = desc;
			
					vcpu->vmcs.guest_GDTR_base = (u32)__limbo_gdt;
					vcpu->vmcs.guest_GDTR_limit = LIMBO_GDT_SIZE - 1;
			}
			
			if(isl_guesthastr == 1){
				vcpu->vmcs.guest_TR_selector=isl_guest_TR_selector;
				vcpu->vmcs.guest_TR_base = isl_guest_TR_base;
				vcpu->vmcs.guest_TR_limit = isl_guest_TR_limit;
				vcpu->vmcs.guest_TR_access_rights = isl_guest_TR_access_rights;
				vcpu->vmcs.guest_LDTR_selector=isl_guest_LDTR_selector;
				vcpu->vmcs.guest_LDTR_base = isl_guest_LDTR_base;
				vcpu->vmcs.guest_LDTR_limit = isl_guest_LDTR_limit;
				vcpu->vmcs.guest_LDTR_access_rights = isl_guest_LDTR_access_rights;
			}else{
				//zero out LDTR 
				vcpu->vmcs.guest_LDTR_selector=0;
				vcpu->vmcs.guest_LDTR_base = 0;
				vcpu->vmcs.guest_LDTR_limit = 0;
				vcpu->vmcs.guest_LDTR_access_rights = 0x10000;
			
			}
			
			//always use limbo pages until we get to proper protected mode
			//printf("\nUsing limbo pages until we get to proper PMODE...");
			vcpu->vmcs.guest_CR3 = __hva2spa__((u32)__runtime_v86_pagedir);
				
			//always make sure we have no IDT, we will load IDT when the
			//guest enters into proper protected-mode from limbo
			vcpu->vmcs.guest_IDTR_base = 0;
			vcpu->vmcs.guest_IDTR_limit = 0;
				
				
			//load guest CR0 and CR4, the v86 monitor has these values
			//stored when it performed a world switch
			vcpu->vmcs.guest_CR4 = v86monitor_guest_reg_cr4;
			vcpu->vmcs.guest_CR0 = v86monitor_guest_reg_cr0;
			//sanitize CR0 and CR4 values for VMX compatibility
			vcpu->vmcs.guest_CR4 |= vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];
			vcpu->vmcs.guest_CR0 |= vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];
				
			//set CR0.WP
			//guest_CR0 |= CR0_WP;
			

			//printf("\nCR0=0x%08lx, CR3=0x%08lx, CR4=0x%08lx",
			//	(unsigned long)guest_CR0, (unsigned long)guest_CR3, 
			//	(unsigned long)guest_CR4);
			
				vcpu->vmcs.guest_ES_selector = 0;
				vcpu->vmcs.guest_DS_selector = 0;
				vcpu->vmcs.guest_FS_selector = 0;
				vcpu->vmcs.guest_GS_selector = 0;

				r->eax = v86monitor_guest_reg_eax;
				r->ebx = v86monitor_guest_reg_ebx;
				r->ecx = v86monitor_guest_reg_ecx;
				r->edx = v86monitor_guest_reg_edx;
				r->ebp = v86monitor_guest_reg_ebp;
				r->esi = v86monitor_guest_reg_esi;
				r->edi = v86monitor_guest_reg_edi;
			
				
				vcpu->vmcs.guest_RSP = v86monitor_guest_reg_esp;
				vcpu->vmcs.guest_RIP = v86monitor_guest_reg_eip;
				
				vcpu->vmcs.guest_RFLAGS = v86monitor_guest_reg_eflags; 
				vcpu->vmcs.guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
				vcpu->vmcs.guest_RFLAGS |= (1<<1);				// reserved 1-bits
				vcpu->vmcs.guest_RFLAGS &= ~(1<<17);	// Virtual-8086 mode = disable
				vcpu->vmcs.guest_RFLAGS &= ~(3<<12);	// IOPL=0 
				//guest_RFLAGS &= ~(1<<9);	// IF disable 
				//guest_RFLAGS &= ~(1<<14);	// NT (Nested Task) disable
				
				vcpu->vmcs.guest_ES_base = 0;
				vcpu->vmcs.guest_CS_base = (u32)(v86monitor_guest_reg_cs * 16);
				vcpu->vmcs.guest_SS_base = (u32)(v86monitor_guest_reg_ss * 16);
				vcpu->vmcs.guest_DS_base = 0;
				vcpu->vmcs.guest_FS_base = 0;
				vcpu->vmcs.guest_GS_base = 0;
				vcpu->vmcs.guest_ES_limit = 0;
				vcpu->vmcs.guest_CS_limit = 0xFFFF;
				vcpu->vmcs.guest_SS_limit = 0xFFFF;
				vcpu->vmcs.guest_DS_limit = 0;
				vcpu->vmcs.guest_FS_limit = 0;
				vcpu->vmcs.guest_GS_limit = 0;
				vcpu->vmcs.guest_ES_access_rights = 0x10000;
				vcpu->vmcs.guest_CS_access_rights = 0x9B;
				vcpu->vmcs.guest_SS_access_rights = 0x93;
				vcpu->vmcs.guest_DS_access_rights = 0x10000;
				vcpu->vmcs.guest_FS_access_rights = 0x10000;
				vcpu->vmcs.guest_GS_access_rights = 0x10000;
				vcpu->vmcs.guest_VMCS_link_pointer_full = ~0L;
				vcpu->vmcs.guest_VMCS_link_pointer_high = ~0L;

        #if defined (__NESTED_PAGING__)
		      vcpu->vmcs.control_VMX_cpu_based |= (1 << 15); //enable CR3 load exiting
		      vcpu->vmcs.control_VMX_cpu_based |= (1 << 16); //enable CR3 store exiting
		    #endif


		//debug
		//printf("\nREAL --> PROTECTED_LIMBO (CS:IP=0x%04x:0x%04x, SS:SP=0x%04x:0x%04x)",
		//				(u16)vcpu->vmcs.guest_CS_selector, (u16)vcpu->vmcs.guest_RIP, (u16)vcpu->vmcs.guest_SS_selector, (u16)vcpu->vmcs.guest_RSP );
      
      #if defined (__NESTED_PAGING__)
			__vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
      #endif

			return(nextstate);
		}	
	// END if(currentstate == GSTATE_REALMODE)
	}else if(currentstate & GSTATE_PROTECTEDMODE){
		//see if we have no GDTR, if so this is a limbo to proper
		//stage, so we just load the GDTR and an optional IDTR if present
		//and setup paging
		if( !(currentstate & GSTATE_PROTECTEDMODE_GDTR) ){
			u64 *gdt;
			u64 desc;
			u32 gran;
			ASSERT(nextstate & GSTATE_PROTECTEDMODE_GDTR);
			
			//debug
			//printf("\nPROTECTED_LIMBO --> PROTECTED");
			//printf("\n	SS:ESP before=0x%04x:0x%08x", guest_SS_selector, (u32)guest_RSP);
			//printf("\n	CS:EIP before=0x%04x:0x%08x", guest_CS_selector, (u32)guest_RIP);

			//printf("\nEntering proper protected mode from limbo");
			//printf("\n	Target CS:EIP=0x%04x:0x%08x",
			//	guest_limbo_cs, guest_limbo_eip);
			//printf("\n	GUEST GDT load (base=0x%08x, limit=0x%04x)",
			//		v86monitor_guest_gdt_base, v86monitor_guest_gdt_limit);
			vcpu->vmcs.guest_GDTR_base = v86monitor_guest_gdt_base;
			vcpu->vmcs.guest_GDTR_limit = v86monitor_guest_gdt_limit;
			if(nextstate & GSTATE_PROTECTEDMODE_IDTR){
				//printf("\n	GUEST IDT load (base=0x%08x, limit=0x%04x)",
				//	v86monitor_guest_idt_base, v86monitor_guest_idt_limit);
				vcpu->vmcs.guest_IDTR_base = v86monitor_guest_idt_base;
				vcpu->vmcs.guest_IDTR_limit = v86monitor_guest_idt_limit;
			}else{
				ASSERT( !(vcpu->vmcs.guest_RFLAGS & EFLAGS_IF) );
				//printf("\n 	NO IDT currently, but interrupts disabled, so no issues");
			}

			vcpu->vmcs.guest_SS_base =0;
			vcpu->vmcs.guest_SS_limit =0;
			vcpu->vmcs.guest_SS_access_rights=0x10000;
			vcpu->vmcs.guest_SS_selector = 0;
			vcpu->vmcs.guest_CS_selector = guest_limbo_cs;
			gdt = (u64 *)(u32)vcpu->vmcs.guest_GDTR_base;
			desc = gdt[vcpu->vmcs.guest_CS_selector >> 3];

			vcpu->vmcs.guest_CS_base = (u32) ( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
			vcpu->vmcs.guest_CS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
			gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
			
			if( (gran==1) && (vcpu->vmcs.guest_CS_limit == 0x000FFFFFUL) )
				vcpu->vmcs.guest_CS_limit = 0xFFFFFFFFUL;
			
			vcpu->vmcs.guest_CS_access_rights = 
				(u32) (((u64)desc & (u64)0x00F0FF0000000000ULL) >> (u64)40);							
			
			
			vcpu->vmcs.guest_RIP = guest_limbo_eip;
			
			
			vcpu->vmcs.guest_ES_selector = 0;
				vcpu->vmcs.guest_DS_selector = 0;
				vcpu->vmcs.guest_FS_selector = 0;
				vcpu->vmcs.guest_GS_selector = 0;
				vcpu->vmcs.guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
				vcpu->vmcs.guest_RFLAGS |= (1<<1);				// reserved 1-bits
				vcpu->vmcs.guest_ES_base = 0;
				vcpu->vmcs.guest_DS_base = 0;
				vcpu->vmcs.guest_FS_base = 0;
				vcpu->vmcs.guest_GS_base = 0;
				vcpu->vmcs.guest_ES_limit = 0;
				vcpu->vmcs.guest_DS_limit = 0;
				vcpu->vmcs.guest_FS_limit = 0;
				vcpu->vmcs.guest_GS_limit = 0;
				vcpu->vmcs.guest_ES_access_rights = 0x10000;
				
				//adjust CS access rights
				vcpu->vmcs.guest_CS_access_rights |= 0x0B;
				
				
				vcpu->vmcs.guest_SS_access_rights = 0x10000;
				vcpu->vmcs.guest_DS_access_rights = 0x10000;
				vcpu->vmcs.guest_FS_access_rights = 0x10000;
				vcpu->vmcs.guest_GS_access_rights = 0x10000;
				vcpu->vmcs.guest_VMCS_link_pointer_full = ~0L;
				vcpu->vmcs.guest_VMCS_link_pointer_high = ~0L;
			
		
			vcpu->vmcs.control_exception_bitmap &= ~(1UL << 13); //disable INT 13 (#GP fault)
			
			if(nextstate & GSTATE_PROTECTEDMODE_PG){
					vcpu->vmcs.guest_CR3  = v86monitor_guest_reg_cr3;

        #if defined (__NESTED_PAGING__)
		      vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
		      vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
        #endif

			}else{
				//guest must be enabling paging by setting CR0.PG later
				guestcr3val_when_cr0_pg_off = v86monitor_guest_reg_cr3;
			}
			
			//setup guest RSP
			vcpu->vmcs.guest_RSP |= limbo_rsp;



      #if defined (__NESTED_PAGING__)
			__vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
      #endif


			return (nextstate);
		}else{
      ASSERT( nextstate == GSTATE_REALMODE);
			//debug
			//printf("\nPROTECTED --> REAL");
			
			//prepare to lock in V86 monitor, all state is already initialized,
			//all we need to do is to initialize the registers
			//load all the segment register base, limits and access rights from 
			//the current selector values
			//loading the v86 monitor destroys LDTR and TR which can be
			//persistent across prot-real-prot if unchanged, so we need to
			//save them here
			isl_guest_TR_selector= vcpu->vmcs.guest_TR_selector;
			isl_guest_TR_base = vcpu->vmcs.guest_TR_base;
			isl_guest_TR_limit = vcpu->vmcs.guest_TR_limit;
			isl_guest_TR_access_rights = vcpu->vmcs.guest_TR_access_rights;
			isl_guest_LDTR_selector=vcpu->vmcs.guest_LDTR_selector;
			isl_guest_LDTR_base = vcpu->vmcs.guest_LDTR_base;
			isl_guest_LDTR_limit = vcpu->vmcs.guest_LDTR_limit;
			isl_guest_LDTR_access_rights = vcpu->vmcs.guest_LDTR_access_rights;
			isl_guesthastr=1;
							
			//save current CR3 value
			v86monitor_guest_reg_cr3 = vcpu->vmcs.guest_CR3;
			
			//setup segment registers			
			{
				u64 *gdt;
				u64 desc;
				u32 gran;
				gdt = (u64 *)(u32)vcpu->vmcs.guest_GDTR_base;
			
				//CS	
				desc = gdt[vcpu->vmcs.guest_CS_selector >> 3];
				vcpu->vmcs.guest_CS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				vcpu->vmcs.guest_CS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				vcpu->vmcs.guest_CS_limit = (vcpu->vmcs.guest_CS_limit * gran);
				if(gran == 4096)
					vcpu->vmcs.guest_CS_limit += 0xFFF;
				vcpu->vmcs.guest_CS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							

				//DS	
				desc = gdt[vcpu->vmcs.guest_DS_selector >> 3];
				vcpu->vmcs.guest_DS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				vcpu->vmcs.guest_DS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				vcpu->vmcs.guest_DS_limit = (vcpu->vmcs.guest_DS_limit * gran);
				if(gran == 4096)
					vcpu->vmcs.guest_DS_limit += 0xFFF;
				vcpu->vmcs.guest_DS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							

				//ES	
				desc = gdt[vcpu->vmcs.guest_ES_selector >> 3];
				vcpu->vmcs.guest_ES_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				vcpu->vmcs.guest_ES_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				vcpu->vmcs.guest_ES_limit = (vcpu->vmcs.guest_ES_limit * gran);
				if(gran == 4096)
					vcpu->vmcs.guest_ES_limit += 0xFFF;
				vcpu->vmcs.guest_ES_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							
			
				//FS	
				desc = gdt[vcpu->vmcs.guest_FS_selector >> 3];
				vcpu->vmcs.guest_FS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				vcpu->vmcs.guest_FS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				vcpu->vmcs.guest_FS_limit = (vcpu->vmcs.guest_FS_limit * gran);
				if(gran == 4096)
					vcpu->vmcs.guest_FS_limit += 0xFFF;
				vcpu->vmcs.guest_FS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							

				//GS	
				desc = gdt[vcpu->vmcs.guest_GS_selector >> 3];
				vcpu->vmcs.guest_GS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				vcpu->vmcs.guest_GS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				vcpu->vmcs.guest_GS_limit = (vcpu->vmcs.guest_GS_limit * gran);
				if(gran == 4096)
					vcpu->vmcs.guest_GS_limit += 0xFFF;
				vcpu->vmcs.guest_GS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							

				//SS	
				desc = gdt[vcpu->vmcs.guest_SS_selector >> 3];
				vcpu->vmcs.guest_SS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				vcpu->vmcs.guest_SS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				vcpu->vmcs.guest_SS_limit = (vcpu->vmcs.guest_SS_limit * gran);
				if(gran == 4096)
					vcpu->vmcs.guest_SS_limit += 0xFFF;
				vcpu->vmcs.guest_SS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							
			
			}


			if(vcpu->vmcs.guest_RFLAGS & (1 << 14)){
				printf("\nGuest has NT bit set, hmm gotta handle this!");
				HALT();
			}

			if(vcpu->vmcs.guest_RFLAGS & (3 << 12)){
				printf("\nGuest has IOPL 3, hmm gotta handle this!");
				HALT();
			}

			vcpu->vmcs.guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
			vcpu->vmcs.guest_RFLAGS |= (1<<1);				// reserved 1-bits
			vcpu->vmcs.guest_RFLAGS |= (1<<17);	// for Virtual-8086 mode
			vcpu->vmcs.guest_RFLAGS |= (3<<12);	// for IO-privilege-level 
			vcpu->vmcs.guest_RFLAGS &= ~(1<<14);	// for NT (Nested Task)
			
			//sanitize guest CR0 for VMX compatibility
			vcpu->vmcs.guest_CR0 |= vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];
			
			vcpu->vmcs.guest_CR3 = __hva2spa__((u32)__runtime_v86_pagedir);
			vcpu->vmcs.guest_VMCS_link_pointer_full = ~0L;
			vcpu->vmcs.guest_VMCS_link_pointer_high = ~0L;
			vcpu->vmcs.guest_IDTR_base = (u32)__runtime_v86_idt;
			vcpu->vmcs.guest_GDTR_base = (u32)__runtime_v86_gdt;
			vcpu->vmcs.guest_LDTR_base = (u32)__runtime_v86_ldt;
			vcpu->vmcs.guest_TR_base   = (u32)__runtime_v86_tss;
			vcpu->vmcs.guest_IDTR_limit = (256 * 8) - 1;	// 256 descriptors
			vcpu->vmcs.guest_GDTR_limit = (3 * 8) - 1;		// 3 descriptors
			vcpu->vmcs.guest_LDTR_limit = (4 * 8) - 1;		// 4 descriptors
			vcpu->vmcs.guest_TR_limit   = (26 * 4) + 0x20 + 0x2000;
			vcpu->vmcs.guest_LDTR_access_rights = 0x82;
			vcpu->vmcs.guest_TR_access_rights   = 0x8B;
			vcpu->vmcs.guest_LDTR_selector = V86M_SELECTOR_LDTR;
			vcpu->vmcs.guest_TR_selector   = V86M_SELECTOR_TASK;
			vcpu->vmcs.guest_ES_access_rights = 0xF3;
			vcpu->vmcs.guest_CS_access_rights = 0xF3;
			vcpu->vmcs.guest_SS_access_rights = 0xF3;
			vcpu->vmcs.guest_DS_access_rights = 0xF3;
			vcpu->vmcs.guest_FS_access_rights = 0xF3;
			vcpu->vmcs.guest_GS_access_rights = 0xF3;
			vcpu->vmcs.guest_CS_selector=vcpu->vmcs.guest_CS_base >> 4;
			vcpu->vmcs.guest_DS_selector=vcpu->vmcs.guest_DS_base >> 4;
			vcpu->vmcs.guest_ES_selector=vcpu->vmcs.guest_ES_base >> 4;
			vcpu->vmcs.guest_FS_selector=vcpu->vmcs.guest_FS_base >> 4;
			vcpu->vmcs.guest_GS_selector=vcpu->vmcs.guest_GS_base >> 4;
			vcpu->vmcs.guest_SS_selector=vcpu->vmcs.guest_SS_base >> 4;
			
			limbo_rsp = vcpu->vmcs.guest_RSP;
			limbo_rsp &= 0xFFFF0000; //clear low 16-bits
			vcpu->vmcs.guest_RSP &= 0x0000FFFF; //clear high 16 bits for guest

			vcpu->vmcs.control_VMX_cpu_based |= (1<<7);	// HLT-exiting

      #if defined (__NESTED_PAGING__)
			__vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
      #endif

      return(nextstate);
		}
  }

	printf("\nCPU(0x%02x): isl_prepareVMCS: invalid combination: 0x%08lx->0x%08lx",
		vcpu->id, (unsigned int)currentstate, (unsigned int)nextstate);
	HALT();
}

//---start a HVM----------------------------------------------------------------
void startHVM(VCPU *vcpu, u32 vmcs_phys_addr){
  //clear VMCS
  if(!__vmx_vmclear((u64)vmcs_phys_addr)){
    printf("\nCPU(0x%02x): VMCLEAR failed, HALT!", vcpu->id);
    HALT();
  }
  printf("\nCPU(0x%02x): VMCLEAR success.", vcpu->id);
  
  
  //set VMCS revision id
 	*((u32 *)vcpu->vmcs_vaddr) = (u32)vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

  //load VMPTR
  if(!__vmx_vmptrld((u64)vmcs_phys_addr)){
    printf("\nCPU(0x%02x): VMPTRLD failed, HALT!", vcpu->id);
    HALT();
  }
  printf("\nCPU(0x%02x): VMPTRLD success.", vcpu->id);
  
  //put VMCS to CPU
  putVMCS(vcpu);
  printf("\nCPU(0x%02x): VMWRITEs success.", vcpu->id);
  ASSERT( vcpu->vmcs.guest_VMCS_link_pointer_full == 0xFFFFFFFFUL );

  {
    extern void startHVM_launch(void);
    startHVM_launch();
    printf("\nCPU(0x%02x): Error in VMLAUNCH. HALT!");
    HALT();
  }

  HALT();
}




//---initVMCS - intialize VMCS for guest boot-----------------------------------
void initVMCS(VCPU *vcpu){
  //setup initial guest state
	printf("\nCPU(0x%02x): Preparing VMCS for launch...", vcpu->id);
	vcpu->guest_currentstate=GSTATE_DEAD;
	vcpu->guest_nextstate=GSTATE_REALMODE;
	vcpu->guest_currentstate=isl_prepareVMCS(vcpu, NULL, vcpu->guest_currentstate, vcpu->guest_nextstate);
	printf("\nDone.");
}


//---HLT intercept handling, used to switch from guest real mode to PE----------
void isl_handleintercept_hlt(VCPU *vcpu, struct regs *r){
	//we should be called when the v86monitor causes a world switch
	//to end real-mode execution
	//sanity check guest state, cr0 contents and gdt
	if( !((vcpu->guest_currentstate == GSTATE_REALMODE) && 
			(v86monitor_guest_reg_cr0 & CR0_PE) &&
			(v86monitor_guest_gdt_base != 0) &&
			(v86monitor_guest_gdt_limit != 0) ) ){
		printf("\nCPU(0x%02x): HLT intercept, undefined guest condition!", vcpu->id);
		HALT();
	}

	//printf("\nCPU(0x%02x): HLT intercept, guest going to protected mode (CR0=0x%08x)...",
//		vcpu->id, v86monitor_guest_reg_cr0);
					
	
	vcpu->guest_nextstate = GSTATE_PROTECTEDMODE;
				
	if(v86monitor_guest_reg_cr0 & CR0_PG)
		vcpu->guest_nextstate |= GSTATE_PROTECTEDMODE_PG;
	
	vcpu->vmcs.control_CR0_shadow = v86monitor_guest_reg_cr0;
		
	vcpu->guest_currentstate = isl_prepareVMCS(vcpu, r, vcpu->guest_currentstate, vcpu->guest_nextstate);
}

//---for switching from protected mode limbo to protected mode proper-----------
void isl_handleintercept_exception_0D(VCPU *vcpu, struct regs *r){
	u32 pcpaddr, stackpaddr;
	ASSERT( (vcpu->guest_currentstate == GSTATE_PROTECTEDMODE) ||
				(vcpu->guest_currentstate == (GSTATE_PROTECTEDMODE | GSTATE_PROTECTEDMODE_PG)) 
				);
	
	pcpaddr = vcpu->vmcs.guest_CS_base + vcpu->vmcs.guest_RIP;
	if(*((u8 *)pcpaddr) == 0xCB){
		//retf
		stackpaddr = vcpu->vmcs.guest_SS_base + (u16)vcpu->vmcs.guest_RSP;
		guest_limbo_eip =  (u32)(*(u16 *)stackpaddr);
		guest_limbo_cs = *(u16 *)((u32)stackpaddr+2);
		vcpu->vmcs.guest_RSP += 4;
	}else if(*((u8 *)pcpaddr) == 0xEA){
 		//jmp sel:off 16-bit off
		guest_limbo_eip = (u32)(*(u16 *)((u32)pcpaddr+1));
		guest_limbo_cs = *(u16 *)((u32)pcpaddr+3);
		vcpu->vmcs.guest_RIP += 5; 		
	}else if(*((u8 *)pcpaddr) == 0x66 && *((u8 *)pcpaddr+1) == 0xEA){
 		//jmp sel:off 32-bit off
		guest_limbo_eip = *(u32 *)((u32)pcpaddr+2);
		guest_limbo_cs = *(u16 *)((u32)pcpaddr+6);
		vcpu->vmcs.guest_RIP += 8; 		
	}else{
		printf("\n%s: unrecognized opcode, dump follows...\n", __FUNCTION__);
		{
			u8 *ch=(u8 *)pcpaddr;
			int i;
			for(i=0; i < 16; i++)
				printf("%02x ", ch[i]);
			printf("\nHalt!");
		}
		HALT();
	}

	vcpu->guest_nextstate = vcpu->guest_currentstate | GSTATE_PROTECTEDMODE_GDTR;
	if( (v86monitor_guest_idt_base != 0) || 
			(v86monitor_guest_idt_limit != 0) )
			vcpu->guest_nextstate |= GSTATE_PROTECTEDMODE_IDTR;
			
	vcpu->guest_currentstate = isl_prepareVMCS(vcpu, r, vcpu->guest_currentstate, vcpu->guest_nextstate);
}

//---CR0 access handler---------------------------------------------------------
//we get here only if any of the bits specified by control_cr0_mask get 
//modified. This includes CR0.PG, CR0.PE, CR0.NE, CR0.ET and CR0.WP 
void handle_intercept_cr0access(VCPU *vcpu, struct regs *r, u32 gpr, u32 tofrom){
	u32 cr0value;
	
	ASSERT(tofrom == VMX_CRX_ACCESS_TO);
	ASSERT( (vcpu->guest_currentstate & GSTATE_PROTECTEDMODE) &&
		(vcpu->guest_currentstate & (GSTATE_PROTECTEDMODE | GSTATE_PROTECTEDMODE_GDTR)) );

  	
	cr0value = *((u32 *)vmx_decode_reg(gpr, vcpu, r));

  //printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x MOV CR0, xx", vcpu->id,
  //      (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
	
	//we handle two situations, CR0_PG being turned on and off while in PMODE
	//PMODE itself turned off (as a result CR0_PG must be turned off)
	if( (cr0value & CR0_PE) && 
			(vcpu->vmcs.control_CR0_shadow & CR0_PG) && !(cr0value & CR0_PG)){
		//printf("\nCPU(0x%02x): Paging disabled", vcpu->id); //paging disabled
    guestcr3val_when_cr0_pg_off = vcpu->vmcs.guest_CR3;
		
		vcpu->vmcs.guest_CR3 = __hva2spa__((u32)__runtime_v86_pagedir);	//load our unity mapping
		vcpu->vmcs.guest_CR4 &= ~(CR4_PAE);	//disable CR4_PAE if enabled
		
		vcpu->vmcs.control_CR0_shadow &= ~(CR0_PG);

		vcpu->vmcs.control_VMX_cpu_based |= (1 << 15); //enable CR3 load exiting
		vcpu->vmcs.control_VMX_cpu_based |= (1 << 16); //enable CR3 store exiting
					
		#if defined(__NESTED_PAGING__)
		//we need CR3 intercepts to catch realmode code that can r/w CR3
    vcpu->vmcs.control_VMX_cpu_based |= (1 << 15); //enable CR3 load exiting
		vcpu->vmcs.control_VMX_cpu_based |= (1 << 16); //enable CR3 store exiting
    #endif

		vcpu->guest_currentstate &= ~(GSTATE_PROTECTEDMODE_PG);
		return;
	}else if 
		((cr0value & CR0_PE) && 
		!(vcpu->vmcs.control_CR0_shadow & CR0_PG) && (cr0value & CR0_PG)){
		//printf("\nCPU(0x%02x): Paging enabled", vcpu->id); //paging enabled

		vcpu->vmcs.control_CR0_shadow |= CR0_PG;

 		vcpu->vmcs.guest_CR3 = guestcr3val_when_cr0_pg_off;


		//if CR4.PAE was manipulated in real-mode, control_CR4_shadow would have
		//the correct PAE bit, so propagate it to CR4 since we had disabled PAE
		//for our unity mapping
		if(vcpu->vmcs.control_CR4_shadow & CR4_PAE){
			vcpu->vmcs.guest_CR4 |= CR4_PAE;

      #if defined(__NESTED_PAGING__)
      //we need to load guest PDPTEs as we emulated CR4 load above
      {
   			u64 pdpte;
  			unsigned offset = (vcpu->vmcs.guest_CR3 & (4096-1)) >> 5;
  			u64 *pdpt = (u64 *) (u32)vcpu->vmcs.guest_CR3;
  
  			printf("\nLoad PDPTE, Guest CR3=0x%08x, offset=%u", (unsigned int)vcpu->vmcs.guest_CR3, offset);
  			pdpte = pdpt[offset+0];
  			printf("\npdpte=0x%016llx", (unsigned long long)pdpte);
  			vcpu->vmcs.guest_PDPTE0_high= (unsigned int)((u64)pdpte >> 32);
  			vcpu->vmcs.guest_PDPTE0_full= (unsigned int)pdpte;
  			pdpte = pdpt[offset+1];
  			printf("\npdpte=0x%016llx", (unsigned long long)pdpte);
  			vcpu->vmcs.guest_PDPTE1_high= (unsigned int)((u64)pdpte >> 32);
  			vcpu->vmcs.guest_PDPTE1_full= (unsigned int)pdpte;
  			pdpte = pdpt[offset+2];
  			printf("\npdpte=0x%016llx", (unsigned long long)pdpte);
  			vcpu->vmcs.guest_PDPTE2_high= (unsigned int)((u64)pdpte >> 32);
  			vcpu->vmcs.guest_PDPTE2_full= (unsigned int)pdpte;
  			pdpte = pdpt[offset+3];
  			printf("\npdpte=0x%016llx", (unsigned long long)pdpte);
  			vcpu->vmcs.guest_PDPTE3_high= (unsigned int)((u64)pdpte >> 32);
  			vcpu->vmcs.guest_PDPTE3_full= (unsigned int)pdpte;
  			
  			printf("\nLoading guest PDPTEs in VMCS:");
  			printf("\nPDPTE0: 0x%08x%08x", vcpu->vmcs.guest_PDPTE0_high, vcpu->vmcs.guest_PDPTE0_full);
  			printf("\nPDPTE1: 0x%08x%08x", vcpu->vmcs.guest_PDPTE1_high, vcpu->vmcs.guest_PDPTE1_full);
  			printf("\nPDPTE2: 0x%08x%08x", vcpu->vmcs.guest_PDPTE2_high, vcpu->vmcs.guest_PDPTE2_full);
  			printf("\nPDPTE3: 0x%08x%08x", vcpu->vmcs.guest_PDPTE3_high, vcpu->vmcs.guest_PDPTE3_full);
      }
      #endif
		  
    }

   

    #if defined (__NESTED_PAGING__)
    //flush EPT mappings as we emulated guest CR3 and CR4 load above
    __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
    #endif


    #if defined(__NESTED_PAGING__)
		//we dont need to intercept CR3 accesses any longer, as we are in pmode 
    vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
		vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
    #endif

		vcpu->guest_currentstate |= (GSTATE_PROTECTEDMODE_PG);

		return;		
	}else if (!(cr0value & CR0_PE)){
		ASSERT(!(cr0value & CR0_PG)); //CR0_PG must be set to 0 if going to real 
		//going from protected to real
		//printf("\nGoing from protected to real...");
		vcpu->guest_nextstate = GSTATE_REALMODE;
		vcpu->vmcs.guest_CR0 = v86monitor_guest_reg_cr0 = cr0value;

		vcpu->vmcs.control_CR0_shadow &= ~(CR0_PG);
		vcpu->vmcs.control_CR0_shadow &= ~(CR0_PE);
		vcpu->guest_currentstate = isl_prepareVMCS(vcpu, r, vcpu->guest_currentstate, vcpu->guest_nextstate);
		return;
	}
	
	printf("\nUnhandled transition of CR0: curr=0x%08lx, next=0x%08lx, mask=0x%08lx, shadow=0x%08lx",
				(unsigned int)vcpu->vmcs.guest_CR0, (unsigned int)cr0value,
					(unsigned int)vcpu->vmcs.control_CR0_mask, (unsigned int)vcpu->vmcs.control_CR0_shadow);
	HALT();
}

//---CR3 access handler---------------------------------------------------------
void handle_intercept_cr3access(VCPU *vcpu, struct regs *r, u32 gpr, u32 tofrom){

  if(vcpu->vmcs.control_CR0_shadow & CR0_PG){
		if(tofrom == VMX_CRX_ACCESS_FROM){
		  //printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x MOV xx, CR3", vcpu->id,
      //  (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);

      *((u32 *)vmx_decode_reg(gpr, vcpu, r)) = vcpu->vmcs.guest_CR3;
		}else{
			vcpu->vmcs.guest_CR3 = *((u32 *)vmx_decode_reg(gpr, vcpu, r));		
		  //printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x MOV CR3, xx", vcpu->id,
      //  (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
		}
	}else{
		//CR3 read/write when CR0.PG is off, blah, we will handle this
		//when CR0.PG is set again
    if(tofrom == VMX_CRX_ACCESS_FROM){
  		 //printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x MOV xx, CR3 (rmode)", vcpu->id,
       // (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);

      *((u32 *)vmx_decode_reg(gpr, vcpu, r)) = guestcr3val_when_cr0_pg_off;
		}else{
		  //printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x MOV CR3, xx (rmode)", vcpu->id,
      //  (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);

			guestcr3val_when_cr0_pg_off = *((u32 *)vmx_decode_reg(gpr, vcpu, r));		
	  }
  }
  
  #if defined(__NESTED_PAGING__)
  //we need to load guest PDPTEs if CR4.PAE=1 if we emulated CR3 load above
  if(tofrom == VMX_CRX_ACCESS_TO && (vcpu->vmcs.guest_CR4 & CR4_PAE) ){
		u64 pdpte;
		unsigned offset = (vcpu->vmcs.guest_CR3 & (4096-1)) >> 5;
		u64 *pdpt = (u64 *) (u32)vcpu->vmcs.guest_CR3;

		printf("\nLoad PDPTE, Guest CR3=0x%08x, offset=%u", (unsigned int)vcpu->vmcs.guest_CR3, offset);
		pdpte = pdpt[offset+0];
		printf("\npdpte=0x%016llx", (unsigned long long)pdpte);
		vcpu->vmcs.guest_PDPTE0_high= (unsigned int)((u64)pdpte >> 32);
		vcpu->vmcs.guest_PDPTE0_full= (unsigned int)pdpte;
		pdpte = pdpt[offset+1];
		printf("\npdpte=0x%016llx", (unsigned long long)pdpte);
		vcpu->vmcs.guest_PDPTE1_high= (unsigned int)((u64)pdpte >> 32);
		vcpu->vmcs.guest_PDPTE1_full= (unsigned int)pdpte;
		pdpte = pdpt[offset+2];
		printf("\npdpte=0x%016llx", (unsigned long long)pdpte);
		vcpu->vmcs.guest_PDPTE2_high= (unsigned int)((u64)pdpte >> 32);
		vcpu->vmcs.guest_PDPTE2_full= (unsigned int)pdpte;
		pdpte = pdpt[offset+3];
		printf("\npdpte=0x%016llx", (unsigned long long)pdpte);
		vcpu->vmcs.guest_PDPTE3_high= (unsigned int)((u64)pdpte >> 32);
		vcpu->vmcs.guest_PDPTE3_full= (unsigned int)pdpte;
		
		printf("\nLoading guest PDPTEs in VMCS:");
		printf("\nPDPTE0: 0x%08x%08x", vcpu->vmcs.guest_PDPTE0_high, vcpu->vmcs.guest_PDPTE0_full);
		printf("\nPDPTE1: 0x%08x%08x", vcpu->vmcs.guest_PDPTE1_high, vcpu->vmcs.guest_PDPTE1_full);
		printf("\nPDPTE2: 0x%08x%08x", vcpu->vmcs.guest_PDPTE2_high, vcpu->vmcs.guest_PDPTE2_full);
		printf("\nPDPTE3: 0x%08x%08x", vcpu->vmcs.guest_PDPTE3_high, vcpu->vmcs.guest_PDPTE3_full);
  } 
  #endif

  
  #if defined (__NESTED_PAGING__)
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
  #endif
}

//---CR4 access handler---------------------------------------------------------
void handle_intercept_cr4access(VCPU *vcpu, struct regs *r, u32 gpr, u32 tofrom){
	ASSERT(tofrom == VMX_CRX_ACCESS_TO);

  //printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x MOV CR4, xx", vcpu->id,
  //  (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
  
  if ( (*((u32 *)vmx_decode_reg(gpr, vcpu, r)) & CR4_PAE) && !(vcpu->vmcs.control_CR4_shadow & CR4_PAE) ){
		//PAE being enabled by guest
		printf("\nPAE enabled by guest.");
		vcpu->vmcs.control_CR4_shadow |= CR4_PAE;
	}else if ( !(*((u32 *)vmx_decode_reg(gpr, vcpu, r)) & CR4_PAE) && (vcpu->vmcs.control_CR4_shadow & CR4_PAE) ) {
		//PAE being disabled by guest
		printf("\nPAE disabled by guest.");
		vcpu->vmcs.control_CR4_shadow &= ~CR4_PAE;
	} else {
		printf("\nMOV TO CR4 (flush TLB?), current=0x%08x, proposed=0x%08x",
			(u32)vcpu->vmcs.guest_CR4, *((u32 *)vmx_decode_reg(gpr, vcpu, r)) );
	}

	//ok, if CR0.PG is off we dont update CR4 now, else blasted VMX
	//will go into an abort especially with M$ coders not adhering to
	//VMX standards or should we say Intel forgot that they had to be
	//backward compatible with the following code from ntldr????...DOH!!!
	//.text:00430DF3                 mov     edx, [esp+arg_0]
	//.text:00430DF7                 mov     ecx, cr3
	//.text:00430DFA                 mov     cr3, ecx
	//.text:00430DFD                 mov     eax, cr0
	//.text:00430E00                 and     eax, 7FFFFFFFh
	//.text:00430E05                 mov     cr0, eax
	//.text:00430E08                 jmp     short $+2
	//.text:00430E0A                 mov     eax, cr4
	//.text:00430E0D                 or      eax, 20h
	//.text:00430E10                 mov     ecx, cr3
	//.text:00430E13                 mov     cr4, eax ;<--- CR4 PAE set BEFORE CR3 loaded with valid PDPT 
	//.text:00430E16                 mov     cr3, edx ;     VMX checks PDPT on CR4 load, but HEY its not valid, so ABORT!!!
	//.text:00430E19                 mov     ecx, cr0
  //.text:00430E1C                 or      ecx, 80000000h
	//.text:00430E22                 mov     cr0, ecx
	//.text:00430E25                 jmp     short $+2
	//.text:00430E27                 retn    4
			
	if(vcpu->vmcs.control_CR0_shadow & CR0_PG){
	  //guest has CR0.PG enabled, so its safe to enable CR4
  	printf("\nCPU(0x%02x): Updating CR4 immediately as CR0.PG=1", vcpu->id);
    vcpu->vmcs.guest_CR4 = *((u32 *)vmx_decode_reg(gpr, vcpu, r));
		vcpu->vmcs.guest_CR4 |= vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];
	
		//TODO: check guest PDPTEs, we need to inject GPF if not valid
	}



  #if defined (__NESTED_PAGING__)
  //we need to flush EPT mappings as we emulated CR4 load above
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
  #endif

}

//---CPUID handling-------------------------------------------------------------
void isl_handleintercept_cpuid(VCPU *vcpu, struct regs *r){
	asm volatile ("cpuid\r\n"
          :"=a"(r->eax), "=b"(r->ebx), "=c"(r->ecx), "=d"(r->edx)
          :"a"(r->eax), "c" (r->ecx));
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}


//------------------------------------------------------------------------------
// guest MSR r/w intercept handling
// HAL invokes NT kernel via SYSENTER if CPU supports it. However,
// regular apps using NTDLL will still use INT 2E if registry entry is not
// tweaked. So, we HAVE to emulate SYSENTER_CS/EIP/ESP to ensure that
// NT kernel doesnt panic with SESSION5_INITIALIZATION_FAILED!
//
// This took me nearly a month of disassembly into the HAL, 
// NTKERNEL and debugging to figure out..eh? 
//
// AMD SVM is neater, only
// when you ask for these MSR intercepts do they get stored and read from
// the VMCB. However, for Intel regardless they get stored and read from VMCS
// for the guest. So we need to have these intercepts bare minimum!!
// A line to this effect would have been much appreciated in the Intel manuals
// doh!!!
//------------------------------------------------------------------------------

//---WRMSR handling-------------------------------------------------------------
void isl_handleintercept_wrmsr(VCPU *vcpu, struct regs *r){
	switch(r->ecx){
		case IA32_SYSENTER_CS_MSR:
			vcpu->vmcs.guest_SYSENTER_CS = (unsigned int)r->eax;
			break;
		case IA32_SYSENTER_EIP_MSR:
			vcpu->vmcs.guest_SYSENTER_EIP = (unsigned long long)r->eax;
			break;
		case IA32_SYSENTER_ESP_MSR:
			vcpu->vmcs.guest_SYSENTER_ESP = (unsigned long long)r->eax;
			break;
		default:{
			asm volatile ("wrmsr\r\n"
          : //no outputs
          :"a"(r->eax), "c" (r->ecx), "d" (r->edx));	
			break;
		}
	}
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}

//---RDMSR handling-------------------------------------------------------------
void isl_handleintercept_rdmsr(VCPU *vcpu, struct regs *r){
	switch(r->ecx){
		case IA32_SYSENTER_CS_MSR:
			r->eax = (u32)vcpu->vmcs.guest_SYSENTER_CS;
			r->edx = 0;
			break;
		case IA32_SYSENTER_EIP_MSR:
			r->eax = (u32)vcpu->vmcs.guest_SYSENTER_EIP;
			r->edx = 0;
			break;
		case IA32_SYSENTER_ESP_MSR:
			r->eax = (u32)vcpu->vmcs.guest_SYSENTER_ESP;
			r->edx = 0;
			break;
		default:{
			asm volatile ("rdmsr\r\n"
          : "=a"(r->eax), "=d"(r->edx)
          : "c" (r->ecx));
			break;
		}
	}
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}

//---EPT voilation handler------------------------------------------------------
void isl_handleintercept_eptviolation(VCPU *vcpu, struct regs *r){
  u32 errorcode, gpa, gva;
	errorcode = (u32)vcpu->vmcs.info_exit_qualification;
	gpa = (u32) vcpu->vmcs.guest_paddr_full;
	gva = (u32) vcpu->vmcs.info_guest_linear_address;

  printf("\nCPU(0x%02x): EPT violation e=0x%08x, gpa=0x%08x, gva=0x%08x",
    vcpu->id, errorcode, gpa, gva);		
  
  {
    //debug, dump the EPT page table entry for the gpa
    u32 pfn = (gpa / PAGE_SIZE_4K);
    u64 *ptables = (u64 *)vmx_ept_p_tables;
    u64 *pml4_table, *pdp_table, *pd_table, *p_table;
    u32 pdpt_index, pd_index, pt_index;
    
    printf("\nptable entry=0x%016llx", ptables[pfn]);
     
  	pml4_table = (u64 *)vmx_ept_pml4_table;
  	pdp_table = (u64 *)__spa2hva__((u32)pml4_table[0] & (u32)0xFFFFF000);
  	pdpt_index = pae_get_pdpt_index(gpa);
    pd_table = (u64 *)__spa2hva__((u32)pdp_table[pdpt_index] & (u32)0xFFFFF000);
    pd_index = pae_get_pdt_index(gpa);
    p_table = (u64 *)__spa2hva__((u32)pd_table[pd_index] & (u32)0xFFFFF000);
    pt_index = pae_get_pt_index(gpa);
        
    printf("\nptable entry=0x%016llx", p_table[pt_index]);
    
  
  }
  
	__vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
  //__vmx_invept(VMX_EPT_SINGLE_CONTEXT, (u64)vcpu->vmcs.control_EPT_pointer_full);
}

//---I/O port access intercept handler------------------------------------------
void isl_handle_intercept_ioportaccess(VCPU *vcpu, struct regs *r){
  u32 access_size, access_type, portnum, stringio;
	u32 app_ret_status;
	
  access_size = (u32)vcpu->vmcs.info_exit_qualification & 0x00000007UL;
	access_type = ((u32)vcpu->vmcs.info_exit_qualification & 0x00000008UL) >> 3;
	portnum =  ((u32)vcpu->vmcs.info_exit_qualification & 0xFFFF0000UL) >> 16;
	stringio = ((u32)vcpu->vmcs.info_exit_qualification & 0x00000010UL) >> 4;
	
  ASSERT(!stringio);	//we dont handle string IO intercepts

  //call our app handler, TODO: it should be possible for an app to
  //NOT want a callback by setting up some parameters during appmain
  app_ret_status=sechyp_app_handleintercept_portaccess(vcpu, r, portnum, access_type, 
          access_size);

  if(app_ret_status == APP_IOINTERCEPT_CHAIN){
   	if(access_type == IO_TYPE_OUT){
  		if( access_size== IO_SIZE_BYTE)
  				outb((u8)r->eax, portnum);
  		else if (access_size == IO_SIZE_WORD)
  				outw((u16)r->eax, portnum);
  		else if (access_size == IO_SIZE_DWORD)
  				outl((u32)r->eax, portnum);	
  	}else{
  		if( access_size== IO_SIZE_BYTE){
  				r->eax &= 0xFFFFFF00UL;	//clear lower 8 bits
  				r->eax |= (u8)inb(portnum);
  		}else if (access_size == IO_SIZE_WORD){
  				r->eax &= 0xFFFF0000UL;	//clear lower 16 bits
  				r->eax |= (u16)inw(portnum);
  		}else if (access_size == IO_SIZE_DWORD){
  				r->eax = (u32)inl(portnum);	
  		}
  	}
  	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;

  }else{
    //skip the IO instruction, app has taken care of it
  	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
  }

	return;
}


//---intercept handler hub------------------------------------------------------
void XtRtmIslInterceptHandler(VCPU *vcpu, struct regs *r){
  getVMCS(vcpu);

  //printf("\nihub: linkptr=0x%08x, 0x%08x", vcpu->vmcs.guest_VMCS_link_pointer_high,
  //    vcpu->vmcs.guest_VMCS_link_pointer_full);
  
  if( (u32)vcpu->vmcs.info_vmexit_reason & 0x80000000UL ){
		printf("\nVM-ENTRY error: reason=0x%08x, qualification=0x%016llx", 
			(u32)vcpu->vmcs.info_vmexit_reason, (u64)vcpu->vmcs.info_exit_qualification);
    dumpVMCS(vcpu);
    HALT();
  }
  
  switch((u32)vcpu->vmcs.info_vmexit_reason){
		case VMEXIT_IOIO:
			{
				isl_handle_intercept_ioportaccess(vcpu, r);
			}
			break;

      case VMEXIT_EPT_VIOLATION:{
		    isl_handleintercept_eptviolation(vcpu, r);
    	}
			break;  	
    
    case VMEXIT_HLT:
			isl_handleintercept_hlt(vcpu, r);
			break;

 		case VMEXIT_EXCEPTION:{
			switch( ((u32)vcpu->vmcs.info_vmexit_interrupt_information & INTR_INFO_VECTOR_MASK) ){
				case 0x0D:
					isl_handleintercept_exception_0D(vcpu, r);
					break;
				
				
				default:
					printf("\nVMEXIT-EXCEPTION:");
					printf("\ncontrol_exception_bitmap=0x%08lx",
						(unsigned long)vcpu->vmcs.control_exception_bitmap);
					printf("\ninterruption information=0x%08lx", 
						(unsigned long)vcpu->vmcs.info_vmexit_interrupt_information);
					printf("\nerrorcode=0x%08lx", 
						(unsigned long)vcpu->vmcs.info_vmexit_interrupt_error_code);
					HALT();
			}
		}
		break;

 		case VMEXIT_CRX_ACCESS:{
			u32 tofrom, gpr, crx; 
			//printf("\nVMEXIT_CRX_ACCESS:");
			//printf("\ninstruction length: %u", info_vmexit_instruction_length);
			crx=(u32) ((u64)vcpu->vmcs.info_exit_qualification & 0x000000000000000FULL);
			gpr=
			 (u32) (((u64)vcpu->vmcs.info_exit_qualification & 0x0000000000000F00ULL) >> (u64)8);
			tofrom = 
			(u32) (((u64)vcpu->vmcs.info_exit_qualification & 0x0000000000000030ULL) >> (u64)4); 
			//printf("\ncrx=%u, gpr=%u, tofrom=%u", crx, gpr, tofrom);
			switch(crx){
				case 0x3: //CR3 access
					handle_intercept_cr3access(vcpu, r, gpr, tofrom);
					break;
				
				case 0x4: //CR4 access
					handle_intercept_cr4access(vcpu, r, gpr, tofrom);
					break;
				
				case 0x0: //CR0 access
					handle_intercept_cr0access(vcpu, r, gpr, tofrom);
					break;
			
				default:
					printf("\nunhandled crx, halting!");
					HALT();
			}
			vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
		}
		break;	

 		case VMEXIT_RDMSR:
			isl_handleintercept_rdmsr(vcpu, r);
			break;
			
		case VMEXIT_WRMSR:
			isl_handleintercept_wrmsr(vcpu, r);
			break;
			
		case VMEXIT_CPUID:
			isl_handleintercept_cpuid(vcpu, r);
			break;

    case VMEXIT_INIT:{
      printf("\nCPU(0x%02x): INIT received (guest shutdown?)", vcpu->id);
      printf("\nCPU(0x%02x): HALTING!", vcpu->id);
      HALT();
    }
    break;
    
    default:{
      printf("\nCPU(0x%02x): Unhandled intercept: 0x%08x", vcpu->id, (u32)vcpu->vmcs.info_vmexit_reason);
      HALT();
    }
  }

  	//check guest interruptibility state
	if(vcpu->vmcs.guest_interruptibility != 0){
		printf("\nWARNING!: interruptibility=%08lx", (unsigned long)vcpu->vmcs.guest_interruptibility);
		vcpu->vmcs.guest_interruptibility = 0;
	}

#if defined(__NESTED_PAGING__)
	if(vcpu->vmcs.info_IDT_vectoring_information & 0x80000000){
				printf("\nCPU(0x%02x): HALT; Nested events unhandled with hwp:0x%08x",
					vcpu->vmcs.info_IDT_vectoring_information);
				HALT();
	}
#endif

  putVMCS(vcpu);
}
