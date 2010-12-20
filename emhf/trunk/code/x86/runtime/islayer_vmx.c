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

//------------------------------------------------------------------------------
// islayer.c
// isolation layer implementation
// author: amit vasudevan (amitvasudevan@acm.org) 
#include <target.h>


//---forward prototypes---------------------------------------------------------
VCPU *getvcpu(void);
void processNMI(VCPU *vcpu, struct regs *r);
void do_quiesce(VCPU *vcpu);

//---globals referenced by this module------------------------------------------
extern u32 __runtime_v86_pagedir[];
//extern u32 __runtime_v86_idt[]; 
extern u32 __runtime_v86_gdt[], __runtime_v86_ldt[], __runtime_v86_tss[];
extern u8 vmx_memregion_iobitmap[];
extern u8 vmx_memregion_msr_area_host[];
extern u8 vmx_memregion_msr_area_guest[];
extern u8 vmx_memregion_ept_pml4_table[];
extern u8 vmx_memregion_ept_pdp_table[];
extern u8 vmx_memregion_ept_pd_tables[];	
extern u8 vmx_memregion_ept_p_tables[]; //4GB	
extern struct __guestmtrrmsrs guestmtrrmsrs[];
extern u8 __limbo_gdt [] ;
extern u8 __limbo_tss [] ;
extern u32 isl_guesthastr;
extern u32 isl_guest_TR_base;
extern u32 isl_guest_TR_access_rights;
extern u32 isl_guest_TR_limit;
extern u16 isl_guest_TR_selector;
extern u32 isl_guest_LDTR_base;
extern u32 isl_guest_LDTR_access_rights;
extern u32 isl_guest_LDTR_limit;
extern u16 isl_guest_LDTR_selector;
extern u32 limbo_rsp;
extern u16 guest_limbo_cs;
extern u32 guest_limbo_eip;
extern u32 guestcr3val_when_cr0_pg_off;
extern const u32 vmx_msr_area_msrs[];
extern const unsigned int vmx_msr_area_msrs_count;
extern struct _vmcsrofields_encodings	vmcsrofields_encodings[];
extern const unsigned int vmcsrofields_encodings_count;
extern struct _vmcsrwfields_encodings	vmcsrwfields_encodings[];
extern const unsigned int vmcsrwfields_encodings_count;
extern u32 x_gdt_start[], x_idt_start[], __runtimetss[];
extern void __islayer_callback(void);
extern u8 vmx_memregion_msrbitmaps[];

//mid-table related externs
extern u32 midtable_numentries;

//core-quiescing related externs
extern u32 quiesce_counter;
extern u32 lock_quiesce_counter; 
extern u32 quiesce_resume_counter;
extern u32 lock_quiesce_resume_counter; 
extern u32 quiesce;      
extern u32 lock_quiesce; 
extern u32 quiesce_resume_signal;
extern u32 lock_quiesce_resume_signal;






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



//---initVT: initializes CPU VT-------------------------------------------------
static void __isl_initVT(VCPU *vcpu){
  //step-1: check if intel CPU
  {
    u8 cpu_oemid[12];
	  asm(	"xor	%%eax, %%eax \n"
				  "cpuid \n"		
				  "mov	%%ebx, %0 \n"
				  "mov	%%edx, %1 \n"
				  "mov	%%ecx, %2 \n"
			     :: "m"(cpu_oemid[0]), "m"(cpu_oemid[4]), "m"(cpu_oemid[8]): "eax", "ebx", "ecx", "edx" );

   	if ( strncmp( cpu_oemid, (u8 *)"GenuineIntel", 12 ) ){
   	  printf("\nCPU(0x%02x) is not an Intel CPU. Halting!", vcpu->id);
   	  HALT();
   	}
  }
  
  //step-2: check VT support
  {
  	u32	cpu_features;
    asm("mov	$1, %%eax \n"
				"cpuid \n"
				"mov	%%ecx, %0	\n"
				::"m"(cpu_features): "eax", "ebx", "ecx", "edx" );
		if ( ( cpu_features & (1<<5) ) == 0 ){
			printf("CPU(0x%02x) does not support VT. Halting!", vcpu->id);
      HALT();
		}
  }

  //step-3: save contents of VMX MSRs as well as MSR EFER and EFCR 
  //into vcpu
  {
    u32 i;
    u32 eax, edx;
    for(i=0; i < IA32_VMX_MSRCOUNT; i++){
        rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
        vcpu->vmx_msrs[i] = (u64)edx << 32 | (u64) eax;        
    }
  
    rdmsr(MSR_EFER, &eax, &edx);
    vcpu->msr_efer = (u64)edx << 32 | (u64) eax;
    rdmsr(MSR_EFCR, &eax, &edx);
    vcpu->msr_efcr = (u64)edx << 32 | (u64) eax;
  
    //[debug: dump contents of MSRs]
    for(i=0; i < IA32_VMX_MSRCOUNT; i++)
       printf("\nCPU(0x%02x): VMX MSR 0x%08x = 0x%08x%08x", vcpu->id, IA32_VMX_BASIC_MSR+i, 
          (u32)((u64)vcpu->vmx_msrs[i] >> 32), (u32)vcpu->vmx_msrs[i]);
    
		//check if VMX supports unrestricted guest, if so we don't need the
		//v86 monitor and the associated state transition handling
		if( (u32)((u64)vcpu->vmx_msrs[IA32_VMX_MSRCOUNT-1] >> 32) & 0x80 )
			vcpu->guest_unrestricted = 1;
		else
			vcpu->guest_unrestricted = 0;
				
		#if defined(__DISABLE_UG__)
		//for now disable unrestricted bit, as we still need to intercept
		//E820 mem-map access and VMX doesnt provide software INT intercept :(
		vcpu->guest_unrestricted=0;
		#endif				
				
		if(vcpu->guest_unrestricted)
			printf("\nCPU(0x%02x): UNRESTRICTED-GUEST supported.", vcpu->id);
		
		printf("\nCPU(0x%02x): MSR_EFER=0x%08x%08x", vcpu->id, (u32)((u64)vcpu->msr_efer >> 32), 
          (u32)vcpu->msr_efer);
    printf("\nCPU(0x%02x): MSR_EFCR=0x%08x%08x", vcpu->id, (u32)((u64)vcpu->msr_efcr >> 32), 
          (u32)vcpu->msr_efcr);
  
  }

  //step-4: enable VMX by setting CR4
	asm(	" mov  %%cr4, %%eax	\n"\
		" bts  $13, %%eax	\n"\
		" mov  %%eax, %%cr4	" ::: "eax" );
  printf("\nCPU(0x%02x): enabled VMX", vcpu->id);

	  //step-5:enter VMX root operation using VMXON
	  {
	  	u32 retval=0;
	  	u64 vmxonregion_paddr = __hva2spa__(vcpu->vmxonregion_vaddr);
	    //set VMCS rev id
	  	*((u32 *)vcpu->vmxonregion_vaddr) = (u32)vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
	    
	   	asm( "vmxon %1 \n"
				 "jbe vmfail \n"
				 "movl $0x1, %%eax \n" 
				 "movl %%eax, %0 \n"
				 "jmp vmsuccess \n"
				 "vmfail: \n"
				 "movl $0x0, %%eax \n"
				 "movl %%eax, %0 \n"
				 "vmsuccess: \n" 
	       : "=m" (retval)
	       : "m"(vmxonregion_paddr) 
	       : "eax");
		
	    if(!retval){
	      printf("\nCPU(0x%02x): Fatal, unable to enter VMX root operation", vcpu->id);
	      HALT();
	    }  
	  
	    printf("\nCPU(0x%02x): Entered VMX root operation", vcpu->id);
	  }
	
}


//---initVMCS - intialize VMCS for guest boot-----------------------------------
static void __isl_initVMCS(VCPU *vcpu){
  if(vcpu->guest_unrestricted){
  	initunrestrictedguestVMCS(vcpu);
  }else{
		//tie in v86 monitor and setup initial guest state
		printf("\nCPU(0x%02x): Preparing VMCS for launch...", vcpu->id);
		vcpu->guest_currentstate=GSTATE_DEAD;
		vcpu->guest_nextstate=GSTATE_REALMODE;
		vcpu->guest_currentstate=isl_prepareVMCS(vcpu, NULL, vcpu->guest_currentstate, vcpu->guest_nextstate);
		printf("\nDone.");
	}
}


//---isolation layer initialization---------------------------------------------
void isl_initialize(VCPU *vcpu){
  //initialize VT
  __isl_initVT(vcpu);

  //initialize VMCS
  __isl_initVMCS(vcpu); 

	
	//initialize CPU MTRRs for guest local copy
	memset((void *)&vcpu->guestmtrrmsrs, 0, sizeof(struct __guestmtrrmsrs) * NUM_MTRR_MSRS);
	
	{
		u32 eax, edx;
		rdmsr(IA32_MTRRCAP, &eax, &edx); 						
		vcpu->guestmtrrmsrs[0].lodword = eax; vcpu->guestmtrrmsrs[0].hidword=edx;
		rdmsr(IA32_MTRR_DEF_TYPE, &eax, &edx); 			
		vcpu->guestmtrrmsrs[1].lodword = eax; vcpu->guestmtrrmsrs[1].hidword=edx;
		rdmsr(IA32_MTRR_FIX64K_00000, &eax, &edx);
		vcpu->guestmtrrmsrs[2].lodword = eax; vcpu->guestmtrrmsrs[2].hidword=edx;
		rdmsr(IA32_MTRR_FIX16K_80000, &eax, &edx);
		vcpu->guestmtrrmsrs[3].lodword = eax; vcpu->guestmtrrmsrs[3].hidword=edx;
		rdmsr(IA32_MTRR_FIX16K_A0000, &eax, &edx);
		vcpu->guestmtrrmsrs[4].lodword = eax; vcpu->guestmtrrmsrs[4].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_C0000, &eax, &edx);	
		vcpu->guestmtrrmsrs[5].lodword = eax; vcpu->guestmtrrmsrs[5].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_C8000, &eax, &edx);	
		vcpu->guestmtrrmsrs[6].lodword = eax; vcpu->guestmtrrmsrs[6].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_D0000, &eax, &edx);	
		vcpu->guestmtrrmsrs[7].lodword = eax; vcpu->guestmtrrmsrs[7].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_D8000, &eax, &edx);	
		vcpu->guestmtrrmsrs[8].lodword = eax; vcpu->guestmtrrmsrs[8].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_E0000, &eax, &edx);	
		vcpu->guestmtrrmsrs[9].lodword = eax; vcpu->guestmtrrmsrs[9].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_E8000, &eax, &edx);	
		vcpu->guestmtrrmsrs[10].lodword = eax; vcpu->guestmtrrmsrs[10].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_F0000, &eax, &edx);	
		vcpu->guestmtrrmsrs[11].lodword = eax; vcpu->guestmtrrmsrs[11].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_F8000, &eax, &edx);	
		vcpu->guestmtrrmsrs[12].lodword = eax; vcpu->guestmtrrmsrs[12].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE0, &eax, &edx);		
		vcpu->guestmtrrmsrs[13].lodword = eax; vcpu->guestmtrrmsrs[13].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK0, &eax, &edx);		
		vcpu->guestmtrrmsrs[14].lodword = eax; vcpu->guestmtrrmsrs[14].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE1, &eax, &edx);		
		vcpu->guestmtrrmsrs[15].lodword = eax; vcpu->guestmtrrmsrs[15].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK1, &eax, &edx);		
		vcpu->guestmtrrmsrs[16].lodword = eax; vcpu->guestmtrrmsrs[16].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE2, &eax, &edx);		
		vcpu->guestmtrrmsrs[17].lodword = eax; vcpu->guestmtrrmsrs[17].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK2, &eax, &edx);		
		vcpu->guestmtrrmsrs[18].lodword = eax; vcpu->guestmtrrmsrs[18].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE3, &eax, &edx);		
		vcpu->guestmtrrmsrs[19].lodword = eax; vcpu->guestmtrrmsrs[19].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK3, &eax, &edx);		
		vcpu->guestmtrrmsrs[20].lodword = eax; vcpu->guestmtrrmsrs[20].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE4, &eax, &edx);		
		vcpu->guestmtrrmsrs[21].lodword = eax; vcpu->guestmtrrmsrs[21].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK4, &eax, &edx);		
		vcpu->guestmtrrmsrs[22].lodword = eax; vcpu->guestmtrrmsrs[22].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE5, &eax, &edx);		
		vcpu->guestmtrrmsrs[23].lodword = eax; vcpu->guestmtrrmsrs[23].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK5, &eax, &edx);		
		vcpu->guestmtrrmsrs[24].lodword = eax; vcpu->guestmtrrmsrs[24].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE6, &eax, &edx);		
		vcpu->guestmtrrmsrs[25].lodword = eax; vcpu->guestmtrrmsrs[25].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK6, &eax, &edx);		
		vcpu->guestmtrrmsrs[26].lodword = eax; vcpu->guestmtrrmsrs[26].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE7, &eax, &edx);		
		vcpu->guestmtrrmsrs[27].lodword = eax; vcpu->guestmtrrmsrs[27].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK7, &eax, &edx);
		vcpu->guestmtrrmsrs[28].lodword = eax; vcpu->guestmtrrmsrs[28].hidword=edx;
	}		
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
  app_ret_status=emhf_app_handleintercept_portaccess(vcpu, r, portnum, access_type, 
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


//---EPT voilation handler------------------------------------------------------
#if defined (__NESTED_PAGING__)
void isl_handleintercept_eptviolation(VCPU *vcpu, struct regs *r){
  u32 errorcode, gpa, gva;
	errorcode = (u32)vcpu->vmcs.info_exit_qualification;
	gpa = (u32) vcpu->vmcs.guest_paddr_full;
	gva = (u32) vcpu->vmcs.info_guest_linear_address;

	//check if EPT violation is due to LAPIC interception
	if(isbsp() && (gpa >= vcpu->lapic_base) && (gpa < (vcpu->lapic_base + PAGE_SIZE_4K)) ){
    lapic_access_handler(vcpu, gpa, errorcode);
  }else{ //no, pass it to emhf app  
	  emhf_app_handleintercept_hwpgtblviolation(vcpu, r, gpa, gva,
  	  (errorcode & 7));
	}		
}
#endif


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
//
//VMX is very picky with MTRR/PAT configuration within EPTs, we have to make
//sure that guest MTRR writes go to its local copy. Technically we will have
//to propagate the writes to the actual MTRRs and update EPTs accordingly, but
//both Linux and Windows do not change default caching policies set by the BIOS
//so for now we are good just accessing local values for read and writes
//------------------------------------------------------------------------------
  
//---WRMSR handling-------------------------------------------------------------
void isl_handleintercept_wrmsr(VCPU *vcpu, struct regs *r){
	//printf("\nCPU(0x%02x): WRMSR 0x%08x", vcpu->id, r->ecx);

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
		//MTRR MSR handling
		case IA32_MTRRCAP: 					vcpu->guestmtrrmsrs[0].hidword= r->edx;  vcpu->guestmtrrmsrs[0].lodword= r->eax;  break;
		case IA32_MTRR_DEF_TYPE: 		vcpu->guestmtrrmsrs[1].hidword= r->edx;  vcpu->guestmtrrmsrs[1].lodword= r->eax;  break;  
		case IA32_MTRR_FIX64K_00000:vcpu->guestmtrrmsrs[2].hidword= r->edx;  vcpu->guestmtrrmsrs[2].lodword= r->eax;  break;
		case IA32_MTRR_FIX16K_80000:vcpu->guestmtrrmsrs[3].hidword= r->edx;  vcpu->guestmtrrmsrs[3].lodword= r->eax;  break;	
		case IA32_MTRR_FIX16K_A0000:vcpu->guestmtrrmsrs[4].hidword= r->edx;  vcpu->guestmtrrmsrs[4].lodword= r->eax;  break;	
		case IA32_MTRR_FIX4K_C0000:	vcpu->guestmtrrmsrs[5].hidword= r->edx;  vcpu->guestmtrrmsrs[5].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_C8000:	vcpu->guestmtrrmsrs[6].hidword= r->edx;  vcpu->guestmtrrmsrs[6].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_D0000:	vcpu->guestmtrrmsrs[7].hidword= r->edx;  vcpu->guestmtrrmsrs[7].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_D8000:	vcpu->guestmtrrmsrs[8].hidword= r->edx;  vcpu->guestmtrrmsrs[8].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_E0000:	vcpu->guestmtrrmsrs[9].hidword= r->edx;  vcpu->guestmtrrmsrs[9].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_E8000:	vcpu->guestmtrrmsrs[10].hidword= r->edx;  vcpu->guestmtrrmsrs[10].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_F0000:	vcpu->guestmtrrmsrs[11].hidword= r->edx;  vcpu->guestmtrrmsrs[11].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_F8000:	vcpu->guestmtrrmsrs[12].hidword= r->edx;  vcpu->guestmtrrmsrs[12].lodword= r->eax;  break;		
		case IA32_MTRR_PHYSBASE0:		vcpu->guestmtrrmsrs[13].hidword= r->edx;  vcpu->guestmtrrmsrs[13].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK0:		vcpu->guestmtrrmsrs[14].hidword= r->edx;  vcpu->guestmtrrmsrs[14].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE1:		vcpu->guestmtrrmsrs[15].hidword= r->edx;  vcpu->guestmtrrmsrs[15].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK1:		vcpu->guestmtrrmsrs[16].hidword= r->edx;  vcpu->guestmtrrmsrs[16].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE2:		vcpu->guestmtrrmsrs[17].hidword= r->edx;  vcpu->guestmtrrmsrs[17].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK2:		vcpu->guestmtrrmsrs[18].hidword= r->edx;  vcpu->guestmtrrmsrs[18].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE3:		vcpu->guestmtrrmsrs[19].hidword= r->edx;  vcpu->guestmtrrmsrs[19].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK3:		vcpu->guestmtrrmsrs[20].hidword= r->edx;  vcpu->guestmtrrmsrs[20].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE4:		vcpu->guestmtrrmsrs[21].hidword= r->edx;  vcpu->guestmtrrmsrs[21].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK4:		vcpu->guestmtrrmsrs[22].hidword= r->edx;  vcpu->guestmtrrmsrs[22].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE5:		vcpu->guestmtrrmsrs[23].hidword= r->edx;  vcpu->guestmtrrmsrs[23].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK5:		vcpu->guestmtrrmsrs[24].hidword= r->edx;  vcpu->guestmtrrmsrs[24].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE6:		vcpu->guestmtrrmsrs[25].hidword= r->edx;  vcpu->guestmtrrmsrs[25].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK6:		vcpu->guestmtrrmsrs[26].hidword= r->edx;  vcpu->guestmtrrmsrs[26].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE7:		vcpu->guestmtrrmsrs[27].hidword= r->edx;  vcpu->guestmtrrmsrs[27].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK7:		vcpu->guestmtrrmsrs[28].hidword= r->edx;  vcpu->guestmtrrmsrs[28].lodword= r->eax;  break;	

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
	//printf("\nCPU(0x%02x): RDMSR 0x%08x", vcpu->id, r->ecx);

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

		//MTRR MSR handling
		case IA32_MTRRCAP: 					r->edx = vcpu->guestmtrrmsrs[0].hidword;  r->eax = vcpu->guestmtrrmsrs[0].lodword;  break;
		case IA32_MTRR_DEF_TYPE: 		r->edx = vcpu->guestmtrrmsrs[1].hidword;  r->eax = vcpu->guestmtrrmsrs[1].lodword;  break;  
		case IA32_MTRR_FIX64K_00000:r->edx = vcpu->guestmtrrmsrs[2].hidword;  r->eax = vcpu->guestmtrrmsrs[2].lodword;  break;
		case IA32_MTRR_FIX16K_80000:r->edx = vcpu->guestmtrrmsrs[3].hidword;  r->eax = vcpu->guestmtrrmsrs[3].lodword;  break;	
		case IA32_MTRR_FIX16K_A0000:r->edx = vcpu->guestmtrrmsrs[4].hidword;  r->eax = vcpu->guestmtrrmsrs[4].lodword;  break;	
		case IA32_MTRR_FIX4K_C0000:	r->edx = vcpu->guestmtrrmsrs[5].hidword;  r->eax = vcpu->guestmtrrmsrs[5].lodword;  break;		
		case IA32_MTRR_FIX4K_C8000:	r->edx = vcpu->guestmtrrmsrs[6].hidword;  r->eax = vcpu->guestmtrrmsrs[6].lodword;  break;		
		case IA32_MTRR_FIX4K_D0000:	r->edx = vcpu->guestmtrrmsrs[7].hidword;  r->eax = vcpu->guestmtrrmsrs[7].lodword;  break;		
		case IA32_MTRR_FIX4K_D8000:	r->edx = vcpu->guestmtrrmsrs[8].hidword;  r->eax = vcpu->guestmtrrmsrs[8].lodword;  break;		
		case IA32_MTRR_FIX4K_E0000:	r->edx = vcpu->guestmtrrmsrs[9].hidword;  r->eax = vcpu->guestmtrrmsrs[9].lodword;  break;		
		case IA32_MTRR_FIX4K_E8000:	r->edx = vcpu->guestmtrrmsrs[10].hidword;  r->eax = vcpu->guestmtrrmsrs[10].lodword;  break;		
		case IA32_MTRR_FIX4K_F0000:	r->edx = vcpu->guestmtrrmsrs[11].hidword;  r->eax = vcpu->guestmtrrmsrs[11].lodword;  break;		
		case IA32_MTRR_FIX4K_F8000:	r->edx = vcpu->guestmtrrmsrs[12].hidword;  r->eax = vcpu->guestmtrrmsrs[12].lodword;  break;		
		case IA32_MTRR_PHYSBASE0:		r->edx = vcpu->guestmtrrmsrs[13].hidword;  r->eax = vcpu->guestmtrrmsrs[13].lodword;  break;			
		case IA32_MTRR_PHYSMASK0:		r->edx = vcpu->guestmtrrmsrs[14].hidword;  r->eax = vcpu->guestmtrrmsrs[14].lodword;  break;			
		case IA32_MTRR_PHYSBASE1:		r->edx = vcpu->guestmtrrmsrs[15].hidword;  r->eax = vcpu->guestmtrrmsrs[15].lodword;  break;			
		case IA32_MTRR_PHYSMASK1:		r->edx = vcpu->guestmtrrmsrs[16].hidword;  r->eax = vcpu->guestmtrrmsrs[16].lodword;  break;			
		case IA32_MTRR_PHYSBASE2:		r->edx = vcpu->guestmtrrmsrs[17].hidword;  r->eax = vcpu->guestmtrrmsrs[17].lodword;  break;			
		case IA32_MTRR_PHYSMASK2:		r->edx = vcpu->guestmtrrmsrs[18].hidword;  r->eax = vcpu->guestmtrrmsrs[18].lodword;  break;			
		case IA32_MTRR_PHYSBASE3:		r->edx = vcpu->guestmtrrmsrs[19].hidword;  r->eax = vcpu->guestmtrrmsrs[19].lodword;  break;			
		case IA32_MTRR_PHYSMASK3:		r->edx = vcpu->guestmtrrmsrs[20].hidword;  r->eax = vcpu->guestmtrrmsrs[20].lodword;  break;			
		case IA32_MTRR_PHYSBASE4:		r->edx = vcpu->guestmtrrmsrs[21].hidword;  r->eax = vcpu->guestmtrrmsrs[21].lodword;  break;			
		case IA32_MTRR_PHYSMASK4:		r->edx = vcpu->guestmtrrmsrs[22].hidword;  r->eax = vcpu->guestmtrrmsrs[22].lodword;  break;			
		case IA32_MTRR_PHYSBASE5:		r->edx = vcpu->guestmtrrmsrs[23].hidword;  r->eax = vcpu->guestmtrrmsrs[23].lodword;  break;			
		case IA32_MTRR_PHYSMASK5:		r->edx = vcpu->guestmtrrmsrs[24].hidword;  r->eax = vcpu->guestmtrrmsrs[24].lodword;  break;			
		case IA32_MTRR_PHYSBASE6:		r->edx = vcpu->guestmtrrmsrs[25].hidword;  r->eax = vcpu->guestmtrrmsrs[25].lodword;  break;			
		case IA32_MTRR_PHYSMASK6:		r->edx = vcpu->guestmtrrmsrs[26].hidword;  r->eax = vcpu->guestmtrrmsrs[26].lodword;  break;			
		case IA32_MTRR_PHYSBASE7:		r->edx = vcpu->guestmtrrmsrs[27].hidword;  r->eax = vcpu->guestmtrrmsrs[27].lodword;  break;			
		case IA32_MTRR_PHYSMASK7:		r->edx = vcpu->guestmtrrmsrs[28].hidword;  r->eax = vcpu->guestmtrrmsrs[28].lodword;  break;	


		default:{
			asm volatile ("rdmsr\r\n"
          : "=a"(r->eax), "=d"(r->edx)
          : "c" (r->ecx));
			break;
		}
	}
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}

//---CPUID handling-------------------------------------------------------------
void isl_handleintercept_cpuid(VCPU *vcpu, struct regs *r){
	//printf("\nCPU(0x%02x): CPUID", vcpu->id);
	asm volatile ("cpuid\r\n"
          :"=a"(r->eax), "=b"(r->ebx), "=c"(r->ecx), "=d"(r->edx)
          :"a"(r->eax), "c" (r->ecx));
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}


//---intercept handler ---------------------------------------------------------
void isl_intercepthandler(VCPU *vcpu, struct regs *r){
  //read VMCS from physical CPU/core
	getVMCS(vcpu);

	//sanity check for VM-entry errors
	if( (u32)vcpu->vmcs.info_vmexit_reason & 0x80000000UL ){
		printf("\nVM-ENTRY error: reason=0x%08x, qualification=0x%016llx", 
			(u32)vcpu->vmcs.info_vmexit_reason, (u64)vcpu->vmcs.info_exit_qualification);
    dumpVMCS(vcpu);
    HALT();
  }
  
  //handle intercepts
  switch((u32)vcpu->vmcs.info_vmexit_reason){
		case VMEXIT_IOIO:
			{
				isl_handle_intercept_ioportaccess(vcpu, r);
			}
			break;

#if defined(__NESTED_PAGING__)
      case VMEXIT_EPT_VIOLATION:{
		    isl_handleintercept_eptviolation(vcpu, r);
    	}
			break;  	
#endif

    case VMEXIT_HLT:
			if(!vcpu->guest_unrestricted){
				isl_handleintercept_hlt(vcpu, r);
			}else{
			 	printf("\nCPU(0x%02x): Unexpected HLT intercept in UG, Halting!", vcpu->id);
				HALT();
			}
			break;

 		case VMEXIT_EXCEPTION:{
			switch( ((u32)vcpu->vmcs.info_vmexit_interrupt_information & INTR_INFO_VECTOR_MASK) ){
				case 0x0D:
					isl_handleintercept_exception_0D(vcpu, r);
					break;

				case 0x01:
					lapic_access_dbexception(vcpu, r);
					break;				
				
				case 0x02:	//NMI
					vcpu->nmiinhvm=1;	//this NMI occured when the core was in guest (HVM)
					processNMI(vcpu, r);
					vcpu->nmiinhvm=0;
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
					if(!vcpu->guest_unrestricted)
						handle_intercept_cr4access(vcpu, r, gpr, tofrom);
					else
						handle_intercept_cr4access_ug(vcpu, r, gpr, tofrom);	
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
      emhf_app_handleshutdown(vcpu, r);      
      printf("\nCPU(0x%02x): warning, emhf_app_handleshutdown returned!", vcpu->id);
    }
    break;

    case VMEXIT_VMCALL:{
      if( emhf_app_handlehypercall(vcpu, r) != APP_SUCCESS){
				printf("\nCPU(0x%02x): error(halt), unhandled hypercall 0x%08x!", vcpu->id, r->eax);
				HALT();
			}
      vcpu->vmcs.guest_RIP += 3;
    }
    break;


		case VMEXIT_TASKSWITCH:{
			u32 idt_v = vcpu->vmcs.info_IDT_vectoring_information & VECTORING_INFO_VALID_MASK;
			u32 type = vcpu->vmcs.info_IDT_vectoring_information & VECTORING_INFO_TYPE_MASK;
			u32 reason = vcpu->vmcs.info_exit_qualification >> 30;
			u16 tss_selector = (u16)vcpu->vmcs.info_exit_qualification;
			
			if(reason == TASK_SWITCH_GATE && type == INTR_TYPE_NMI){
	      printf("\nCPU(0x%02x): NMI received (MP guest shutdown?)", vcpu->id);
	      emhf_app_handleshutdown(vcpu, r);      
  	    printf("\nCPU(0x%02x): warning, emhf_app_handleshutdown returned!", vcpu->id);
    		printf("\nCPU(0x%02x): HALTING!", vcpu->id);
	      HALT();
			}else{
				printf("\nCPU(0x%02x): Unhandled Task Switch. Halt!", vcpu->id);
				printf("\n	idt_v=0x%08x, type=0x%08x, reason=0x%08x, tsssel=0x%04x",
					idt_v, type, reason, tss_selector); 
			}
    	HALT();
		}
		break;

    
    default:{
      printf("\nCPU(0x%02x): Unhandled intercept: 0x%08x", vcpu->id, (u32)vcpu->vmcs.info_vmexit_reason);
      printf("\n	CPU(0x%02x): EFLAGS=0x%08x", vcpu->id, (u32)vcpu->vmcs.guest_RFLAGS);
			printf("\n	SS:ESP =0x%04x:0x%08x", (u16)vcpu->vmcs.guest_SS_selector, (u32)vcpu->vmcs.guest_RSP);
			printf("\n	CS:EIP =0x%04x:0x%08x", (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
			printf("\n	IDTR base:limit=0x%08x:0x%04x", (u32)vcpu->vmcs.guest_IDTR_base,
					(u16)vcpu->vmcs.guest_IDTR_limit);
			//printf("\n 	runtime_v86_idt_base=0x%08x", (u32)__runtime_v86_idt);
			printf("\n	GDTR base:limit=0x%08x:0x%04x", (u32)vcpu->vmcs.guest_GDTR_base,
					(u16)vcpu->vmcs.guest_GDTR_limit);
			//printf("\n 	runtime_v86_idt_base=0x%08x", (u32)__runtime_v86_idt);
     	if(vcpu->vmcs.info_IDT_vectoring_information & 0x80000000){
				printf("\nCPU(0x%02x): HALT; Nested events unhandled 0x%08x",
					vcpu->id, vcpu->vmcs.info_IDT_vectoring_information);
			}


			HALT();
    }
  }

 	//check and clear guest interruptibility state
	if(vcpu->vmcs.guest_interruptibility != 0){
		//printf("\nWARNING!: interruptibility=%08lx", (unsigned long)vcpu->vmcs.guest_interruptibility);
		vcpu->vmcs.guest_interruptibility = 0;
	}

	//make sure we have no nested events
	if(vcpu->vmcs.info_IDT_vectoring_information & 0x80000000){
				printf("\nCPU(0x%02x): HALT; Nested events unhandled with hwp:0x%08x",
					vcpu->id, vcpu->vmcs.info_IDT_vectoring_information);
				HALT();
	}

	//write updated VMCS back to CPU
  putVMCS(vcpu);
  if(vcpu->vmcs.guest_RIP == 0x7c00){
		printf("\nCPU(0x%02x): We are starting at guest boot-sector...", vcpu->id);
	}
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


//---quiescing implementation---------------------------------------------------
void send_quiesce_signal(VCPU *vcpu){
  u32 *icr_low = (u32 *)(0xFEE00000 + 0x300);
  u32 *icr_high = (u32 *)(0xFEE00000 + 0x310);
  u32 icr_high_value= 0xFFUL << 24;
  u32 prev_icr_high_value;
    
  prev_icr_high_value = *icr_high;
  
  *icr_high = icr_high_value;    //send to all but self
  *icr_low = 0x000C0400UL;      //send NMI        
  
  //restore icr high
  *icr_high = prev_icr_high_value;
    
  printf("\nCPU(0x%02x): NMIs fired!", vcpu->id);
}


void do_quiesce(VCPU *vcpu){
        printf("\nCPU(0x%02x): got quiesce signal...", vcpu->id);
        //grab hold of quiesce lock
        spin_lock(&lock_quiesce);
        printf("\nCPU(0x%02x): grabbed quiesce lock.", vcpu->id);

        spin_lock(&lock_quiesce_counter);
        quiesce_counter=0;
        spin_unlock(&lock_quiesce_counter);
        
        //send all the other CPUs the quiesce signal
        quiesce=1;  //we are now processing quiesce
        send_quiesce_signal(vcpu);
        
        //wait for all the remaining CPUs to quiesce
        printf("\nCPU(0x%02x): waiting for other CPUs to respond...", vcpu->id);
        while(quiesce_counter < (midtable_numentries-1) );
        printf("\nCPU(0x%02x): all CPUs quiesced successfully.", vcpu->id);
        
        //perform operation now with all CPUs halted...
        
        //set resume signal to resume the cores that are quiesced
        //Note: we do not need a spinlock for this since we are in any
        //case the only core active until this point
        quiesce_resume_counter=0;
        printf("\nCPU(0x%02x): waiting for other CPUs to resume...", vcpu->id);
        quiesce_resume_signal=1;
        
        while(quiesce_resume_counter < (midtable_numentries-1) );

        quiesce=0;  // we are out of quiesce at this point

        printf("\nCPU(0x%02x): all CPUs resumed successfully.", vcpu->id);
        
        //reset resume signal
        spin_lock(&lock_quiesce_resume_signal);
        quiesce_resume_signal=0;
        spin_unlock(&lock_quiesce_resume_signal);
                
        //release quiesce lock
        printf("\nCPU(0x%02x): releasing quiesce lock.", vcpu->id);
        spin_unlock(&lock_quiesce);
        
        //printf("\nCPU(0x%02x): Halting!", vcpu->id);
        //HALT();
}

//---NMI processing routine-----------------------------------------------------
void processNMI(VCPU *vcpu, struct regs *r){
  
	if( (!vcpu->nmiinhvm) && (!quiesce) ){
    printf("\nCPU(0x%02x): Spurious NMI within hypervisor. halt!", vcpu->id);
    HALT();
  }

	if(quiesce){
    //ok this NMI is because of quiesce. note: quiesce can be 1 and
    //this could be a NMI for the guest. we have no way of distinguising
    //this. however, since quiesce=1, we can handle this NMI as a quiesce NMI
    //and rely on the platform h/w to reissue the NMI later
    printf("\nCPU(0x%02x): NMI for core quiesce", vcpu->id);
    printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x", vcpu->id, (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
  
    printf("\nCPU(0x%02x): quiesced, updating counter. awaiting EOQ...", vcpu->id);
    spin_lock(&lock_quiesce_counter);
    quiesce_counter++;
    spin_unlock(&lock_quiesce_counter);
    
    while(!quiesce_resume_signal);
    printf("\nCPU(0x%02x): EOQ received, resuming...", vcpu->id);
    
    spin_lock(&lock_quiesce_resume_counter);
    quiesce_resume_counter++;
    spin_unlock(&lock_quiesce_resume_counter);
    
    //printf("\nCPU(0x%08x): Halting!", vcpu->id);
    //HALT();
    
  }else{
    //we are not in quiesce, so simply inject this NMI back to guest
    ASSERT( vcpu->nmiinhvm == 1 );
    printf("\nCPU(0x%02x): Regular NMI, injecting back to guest...", vcpu->id);
		vcpu->vmcs.control_VM_entry_exception_errorcode = 0;
					vcpu->vmcs.control_VM_entry_interruption_information = NMI_VECTOR |
			     INTR_TYPE_NMI |
			     INTR_INFO_VALID_MASK;
  }
  
  
}


//---generic exception handler--------------------------------------------------
void isl_exceptionhandler(u32 vector, struct regs *r){
	VCPU *vcpu = getvcpu();
  INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *noecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *)((u32)r->esp + (u32)0x0C);
  INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *ecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *)((u32)r->esp + (u32)0x0C);

  printf("\nCPU(0x%02x): %s excp=0x%08x", vcpu->id, __FUNCTION__, vector);
  printf("\nCPU(0x%02x): %s ESP=0x%08x", vcpu->id, __FUNCTION__, r->esp);
  
	if(vector == NMI_VECTOR){
    processNMI(vcpu, r);
    return;
  }	
  HALT();
}
