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
// islayer_vmx.c - VMX isolation layer implementation
// author: amit vasudevan (amitvasudevan@acm.org) 

#include <emhf.h> 

//==============================================================================
// static (local) data
//==============================================================================



//==============================================================================
// static (local) function definitions
//==============================================================================
static void _vmx_lib_reboot(VCPU *vcpu);
u8 *_vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);

//---initVT: initializes CPU VT-------------------------------------------------
static void _vmx_initVT(VCPU *vcpu){
	//step-0: to enable VMX on a core, we require it to have a TR loaded,
	//so load it for this core
	__vmx_loadTR();


  //step-1: check if intel CPU
  {
    char cpu_oemid[12];
	  asm(	"xor	%%eax, %%eax \n"
				  "cpuid \n"		
				  "mov	%%ebx, %0 \n"
				  "mov	%%edx, %1 \n"
				  "mov	%%ecx, %2 \n"
			     :: "m"(cpu_oemid[0]), "m"(cpu_oemid[4]), "m"(cpu_oemid[8]): "eax", "ebx", "ecx", "edx" );

   	if ( strncmp( cpu_oemid, "GenuineIntel", 12 ) ){
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
    vcpu->vmx_msr_efer = (u64)edx << 32 | (u64) eax;
    rdmsr(MSR_EFCR, &eax, &edx);
    vcpu->vmx_msr_efcr = (u64)edx << 32 | (u64) eax;
  
    //[debug: dump contents of MSRs]
    for(i=0; i < IA32_VMX_MSRCOUNT; i++)
       printf("\nCPU(0x%02x): VMX MSR 0x%08x = 0x%08x%08x", vcpu->id, IA32_VMX_BASIC_MSR+i, 
          (u32)((u64)vcpu->vmx_msrs[i] >> 32), (u32)vcpu->vmx_msrs[i]);
    
		//check if VMX supports unrestricted guest, if so we don't need the
		//v86 monitor and the associated state transition handling
		if( (u32)((u64)vcpu->vmx_msrs[IA32_VMX_MSRCOUNT-1] >> 32) & 0x80 )
			vcpu->vmx_guest_unrestricted = 1;
		else
			vcpu->vmx_guest_unrestricted = 0;
				
		#if defined(__DISABLE_UG__)
		//for now disable unrestricted bit, as we still need to intercept
		//E820 mem-map access and VMX doesnt provide software INT intercept :(
		vcpu->guest_unrestricted=0;
		#endif				
				
		if(vcpu->vmx_guest_unrestricted)
			printf("\nCPU(0x%02x): UNRESTRICTED-GUEST supported.", vcpu->id);
		
		printf("\nCPU(0x%02x): MSR_EFER=0x%08x%08x", vcpu->id, (u32)((u64)vcpu->vmx_msr_efer >> 32), 
          (u32)vcpu->vmx_msr_efer);
    printf("\nCPU(0x%02x): MSR_EFCR=0x%08x%08x", vcpu->id, (u32)((u64)vcpu->vmx_msr_efcr >> 32), 
          (u32)vcpu->vmx_msr_efcr);
  
  }

  //step-4: enable VMX by setting CR4
	asm(	" mov  %%cr4, %%eax	\n"\
		" bts  $13, %%eax	\n"\
		" mov  %%eax, %%cr4	" ::: "eax" );
  printf("\nCPU(0x%02x): enabled VMX", vcpu->id);

	  //step-5:enter VMX root operation using VMXON
	  {
	  	u32 retval=0;
	  	u64 vmxonregion_paddr = __hva2spa__((void*)vcpu->vmx_vmxonregion_vaddr);
	    //set VMCS rev id
	  	*((u32 *)vcpu->vmx_vmxonregion_vaddr) = (u32)vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
	    
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
static void _vmx_initVMCS(VCPU *vcpu){
  if(vcpu->vmx_guest_unrestricted){
  	vmx_initunrestrictedguestVMCS(vcpu);
  }else{
		//tie in v86 monitor and setup initial guest state
		//printf("\nCPU(0x%02x): Preparing VMCS for launch...", vcpu->id);
		//vcpu->guest_currentstate=GSTATE_DEAD;
		//vcpu->guest_nextstate=GSTATE_REALMODE;
		//vcpu->guest_currentstate=isl_prepareVMCS(vcpu, NULL, vcpu->guest_currentstate, vcpu->guest_nextstate);
		//printf("\nDone.");
		printf("\nHALT: Fatal, v86 monitor based real-mode exec. unsupported!");
		HALT();
	}
}

//---function to obtain the vcpu of the currently executing core----------------
//note: this always returns a valid VCPU pointer
VCPU *_vmx_getvcpu(void){
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
  return NULL; /* currently unreachable */
}



//---putVMCS--------------------------------------------------------------------
// routine takes vcpu vmcsfields and stores it in the CPU VMCS 
void _vmx_putVMCS(VCPU *vcpu){
    unsigned int i;
    for(i=0; i < g_vmx_vmcsrwfields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)g_vmx_vmcsrwfields_encodings[i].fieldoffset);
      u32 fieldvalue = *field;
      //printf("\nvmwrite: enc=0x%08x, value=0x%08x", vmcsrwfields_encodings[i].encoding, fieldvalue);
      if(!__vmx_vmwrite(g_vmx_vmcsrwfields_encodings[i].encoding, fieldvalue)){
        printf("\nCPU(0x%02x): VMWRITE failed. HALT!", vcpu->id);
        HALT();
      }
    }
}

//---getVMCS--------------------------------------------------------------------
// routine takes CPU VMCS and stores it in vcpu vmcsfields  
void _vmx_getVMCS(VCPU *vcpu){
  unsigned int i;
  for(i=0; i < g_vmx_vmcsrwfields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)g_vmx_vmcsrwfields_encodings[i].fieldoffset);
      __vmx_vmread(g_vmx_vmcsrwfields_encodings[i].encoding, field);
  }  
  for(i=0; i < g_vmx_vmcsrofields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)g_vmx_vmcsrofields_encodings[i].fieldoffset);
      __vmx_vmread(g_vmx_vmcsrofields_encodings[i].encoding, field);
  }  
}

//--debug: dumpVMCS dumps VMCS contents-----------------------------------------
void _vmx_dumpVMCS(VCPU *vcpu){
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



//---start a HVM----------------------------------------------------------------
static void _vmx_start_hvm(VCPU *vcpu, u32 vmcs_phys_addr){
  //clear VMCS
  if(!__vmx_vmclear((u64)vmcs_phys_addr)){
    printf("\nCPU(0x%02x): VMCLEAR failed, HALT!", vcpu->id);
    HALT();
  }
  printf("\nCPU(0x%02x): VMCLEAR success.", vcpu->id);
  
  
  //set VMCS revision id
 	*((u32 *)vcpu->vmx_vmcs_vaddr) = (u32)vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

  //load VMPTR
  if(!__vmx_vmptrld((u64)vmcs_phys_addr)){
    printf("\nCPU(0x%02x): VMPTRLD failed, HALT!", vcpu->id);
    HALT();
  }
  printf("\nCPU(0x%02x): VMPTRLD success.", vcpu->id);
  
  //put VMCS to CPU
  _vmx_putVMCS(vcpu);
  printf("\nCPU(0x%02x): VMWRITEs success.", vcpu->id);
  ASSERT( vcpu->vmcs.guest_VMCS_link_pointer_full == 0xFFFFFFFFUL );

  {
    u32 errorcode;
    errorcode=__vmx_start_hvm();
    ASSERT(errorcode != 2);	//this means the VMLAUNCH implementation violated the specs.
    //get CPU VMCS into VCPU structure
    _vmx_getVMCS(vcpu);
    
    switch(errorcode){
			case 0:	//no error code, VMCS pointer is invalid
			    printf("\nCPU(0x%02x): VMLAUNCH error; VMCS pointer invalid?. HALT!", vcpu->id);
				break;
			case 1:{//error code available, so dump it
				u32 code=5;
				__vmx_vmread(0x4400, &code);
			    printf("\nCPU(0x%02x): VMLAUNCH error; code=0x%x. HALT!", vcpu->id, code);
				break;
			}
	}
    HALT();
  }

  HALT();
}


/*//---quiescing implementation---------------------------------------------------
static void _vmx_send_quiesce_signal(VCPU *vcpu){
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
}*/







//---vmx int 15 hook enabling function------------------------------------------
static void	_vmx_int15_initializehook(VCPU *vcpu){
	//we should only be called from the BSP
	ASSERT(vcpu->isbsp);
	
	{
		u8 *bdamemory = (u8 *)0x4AC;				//use BDA reserved memory at 0040:00AC
		
		u16 *ivt_int15 = (u16 *)(0x54);			//32-bit CS:IP for IVT INT 15 handler
		
		//printf("\nCPU(0x%02x): original BDA dump: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);
		
		printf("\nCPU(0x%02x): original INT 15h handler at 0x%04x:0x%04x", vcpu->id,
			ivt_int15[1], ivt_int15[0]);

		//we need 8 bytes (4 for the VMCALL followed by IRET and 4 for he original 
		//IVT INT 15h handler address, zero them to start off
		memset(bdamemory, 0x0, 8);		

		//printf("\nCPU(0x%02x): BDA dump after clear: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);

		//implant VMCALL followed by IRET at 0040:04AC
		bdamemory[0]= 0x0f;	//VMCALL						
		bdamemory[1]= 0x01;
		bdamemory[2]= 0xc1;																	
		bdamemory[3]= 0xcf;	//IRET
		
		//store original INT 15h handler CS:IP following VMCALL and IRET
		*((u16 *)(&bdamemory[4])) = ivt_int15[0];	//original INT 15h IP
		*((u16 *)(&bdamemory[6])) = ivt_int15[1];	//original INT 15h CS

		//printf("\nCPU(0x%02x): BDA dump after hook implant: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);

		//point IVT INT15 handler to the VMCALL instruction
		ivt_int15[0]=0x00AC;
		ivt_int15[1]=0x0040;					
	}
}



//==============================================================================
//isolation layer abstraction global functions
//==============================================================================

//---initialize-----------------------------------------------------------------
void vmx_initialize(VCPU *vcpu){
  //initialize VT
  _vmx_initVT(vcpu);

  //initialize VMCS
  _vmx_initVMCS(vcpu); 

	//initialize CPU MTRRs for guest local copy
	memset((void *)&vcpu->vmx_guestmtrrmsrs, 0, sizeof(struct _guestmtrrmsrs) * NUM_MTRR_MSRS);
	
	{
		u32 eax, edx;
		rdmsr(IA32_MTRRCAP, &eax, &edx); 						
		vcpu->vmx_guestmtrrmsrs[0].lodword = eax; vcpu->vmx_guestmtrrmsrs[0].hidword=edx;
		rdmsr(IA32_MTRR_DEF_TYPE, &eax, &edx); 			
		vcpu->vmx_guestmtrrmsrs[1].lodword = eax; vcpu->vmx_guestmtrrmsrs[1].hidword=edx;
		rdmsr(IA32_MTRR_FIX64K_00000, &eax, &edx);
		vcpu->vmx_guestmtrrmsrs[2].lodword = eax; vcpu->vmx_guestmtrrmsrs[2].hidword=edx;
		rdmsr(IA32_MTRR_FIX16K_80000, &eax, &edx);
		vcpu->vmx_guestmtrrmsrs[3].lodword = eax; vcpu->vmx_guestmtrrmsrs[3].hidword=edx;
		rdmsr(IA32_MTRR_FIX16K_A0000, &eax, &edx);
		vcpu->vmx_guestmtrrmsrs[4].lodword = eax; vcpu->vmx_guestmtrrmsrs[4].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_C0000, &eax, &edx);	
		vcpu->vmx_guestmtrrmsrs[5].lodword = eax; vcpu->vmx_guestmtrrmsrs[5].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_C8000, &eax, &edx);	
		vcpu->vmx_guestmtrrmsrs[6].lodword = eax; vcpu->vmx_guestmtrrmsrs[6].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_D0000, &eax, &edx);	
		vcpu->vmx_guestmtrrmsrs[7].lodword = eax; vcpu->vmx_guestmtrrmsrs[7].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_D8000, &eax, &edx);	
		vcpu->vmx_guestmtrrmsrs[8].lodword = eax; vcpu->vmx_guestmtrrmsrs[8].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_E0000, &eax, &edx);	
		vcpu->vmx_guestmtrrmsrs[9].lodword = eax; vcpu->vmx_guestmtrrmsrs[9].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_E8000, &eax, &edx);	
		vcpu->vmx_guestmtrrmsrs[10].lodword = eax; vcpu->vmx_guestmtrrmsrs[10].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_F0000, &eax, &edx);	
		vcpu->vmx_guestmtrrmsrs[11].lodword = eax; vcpu->vmx_guestmtrrmsrs[11].hidword=edx;
		rdmsr(IA32_MTRR_FIX4K_F8000, &eax, &edx);	
		vcpu->vmx_guestmtrrmsrs[12].lodword = eax; vcpu->vmx_guestmtrrmsrs[12].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE0, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[13].lodword = eax; vcpu->vmx_guestmtrrmsrs[13].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK0, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[14].lodword = eax; vcpu->vmx_guestmtrrmsrs[14].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE1, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[15].lodword = eax; vcpu->vmx_guestmtrrmsrs[15].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK1, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[16].lodword = eax; vcpu->vmx_guestmtrrmsrs[16].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE2, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[17].lodword = eax; vcpu->vmx_guestmtrrmsrs[17].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK2, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[18].lodword = eax; vcpu->vmx_guestmtrrmsrs[18].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE3, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[19].lodword = eax; vcpu->vmx_guestmtrrmsrs[19].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK3, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[20].lodword = eax; vcpu->vmx_guestmtrrmsrs[20].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE4, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[21].lodword = eax; vcpu->vmx_guestmtrrmsrs[21].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK4, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[22].lodword = eax; vcpu->vmx_guestmtrrmsrs[22].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE5, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[23].lodword = eax; vcpu->vmx_guestmtrrmsrs[23].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK5, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[24].lodword = eax; vcpu->vmx_guestmtrrmsrs[24].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE6, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[25].lodword = eax; vcpu->vmx_guestmtrrmsrs[25].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK6, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[26].lodword = eax; vcpu->vmx_guestmtrrmsrs[26].hidword=edx;
		rdmsr(IA32_MTRR_PHYSBASE7, &eax, &edx);		
		vcpu->vmx_guestmtrrmsrs[27].lodword = eax; vcpu->vmx_guestmtrrmsrs[27].hidword=edx;
		rdmsr(IA32_MTRR_PHYSMASK7, &eax, &edx);
		vcpu->vmx_guestmtrrmsrs[28].lodword = eax; vcpu->vmx_guestmtrrmsrs[28].hidword=edx;
	}
	
	//INT 15h E820 hook enablement for VMX unrestricted guest mode
	//note: this only happens for the BSP
	if(vcpu->isbsp){
		printf("\nCPU(0x%02x, BSP): initializing INT 15 hook for UG mode...", vcpu->id);
		_vmx_int15_initializehook(vcpu);
	}
			
}

/*
//---generic exception handler--------------------------------------------------
void vmx_runtime_exception_handler(u32 vector, struct regs *r){
	VCPU *vcpu = _vmx_getvcpu();
   //INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *noecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *)((u32)r->esp + (u32)0x0C); 
   //INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *ecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *)((u32)r->esp + (u32)0x0C); 

  printf("\nCPU(0x%02x): %s excp=0x%08x", vcpu->id, __FUNCTION__, vector);
  printf("\nCPU(0x%02x): %s ESP=0x%08x", vcpu->id, __FUNCTION__, r->esp);
  
	if(vector == NMI_VECTOR){
    //_vmx_processNMI(vcpu, r);
    emhf_smpguest_eventhandler_nmiexception(vcpu, r);
    return;
  }	
}*/


//---isbsp----------------------------------------------------------------------
//returns 1 if the calling CPU is the BSP, else 0
u32 vmx_isbsp(void){
  u32 eax, edx;
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  
  if(eax & 0x100)
    return 1;
  else
    return 0;
}



//---wakeup_aps-----------------------------------------------------------------
//wake up application processors (cores) in the system
void vmx_wakeup_aps(void){
	//step-1: setup AP boot-strap code at in the desired physical memory location 
	//note that we need an address < 1MB since the APs are woken up in real-mode
	//we choose 0x10000 physical or 0x1000:0x0000 logical
    {
        _ap_cr3_value = read_cr3();
        _ap_cr4_value = read_cr4();
        memcpy((void *)0x10000, (void *)_ap_bootstrap_start, (u32)_ap_bootstrap_end - (u32)_ap_bootstrap_start + 1);
    }
	
    //step-2: wake up the APs sending the INIT-SIPI-SIPI sequence as per the
    //MP protocol. Use the APIC for IPI purposes.
    if(!txt_is_launched()) { // XXX TODO: Do actual GETSEC[WAKEUP] in here?
        printf("\nBSP: Using APIC to awaken APs...");
        vmx_apic_wakeupAPs(); // apic_vmx.c
        printf("\nBSP: APs should be awake.");
    }else{
		//we ran SENTER, so do a GETSEC[WAKEUP]
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        sinit_mle_data_t *sinit_mle_data;
        os_sinit_data_t *os_sinit_data;

        /* sl.c unity-maps 0xfed00000 for 2M so these should work fine */
        txt_heap = get_txt_heap();
        //printf("\ntxt_heap = 0x%08x", (u32)txt_heap);
        os_mle_data = get_os_mle_data_start(txt_heap);
        //printf("\nos_mle_data = 0x%08x", (u32)os_mle_data);
        sinit_mle_data = get_sinit_mle_data_start(txt_heap);
        //printf("\nsinit_mle_data = 0x%08x", (u32)sinit_mle_data);
        os_sinit_data = get_os_sinit_data_start(txt_heap);
        //printf("\nos_sinit_data = 0x%08x", (u32)os_sinit_data);
            
        /* Start APs.  Choose wakeup mechanism based on
         * capabilities used. MLE Dev Guide says MLEs should
         * support both types of Wakeup mechanism. */

        /* We are jumping straight into the 32-bit portion of the
         * unity-mapped trampoline that starts at 64K
         * physical. Without SENTER, or with AMD, APs start in
         * 16-bit mode.  We get to skip that. */
        printf("\nBSP: _mle_join_start = 0x%08x, _ap_bootstrap_start = 0x%08x",
			(u32)_mle_join_start, (u32)_ap_bootstrap_start);

        /* enable SMIs on BSP before waking APs (which will enable them on APs)
           because some SMM may take immediate SMI and hang if AP gets in first */
        //printf("Enabling SMIs on BSP\n");
        //__getsec_smctrl();
                
        /* MLE Join structure constructed in runtimesup.S. Debug print. */
        mle_join = (mle_join_t*)((u32)_mle_join_start - (u32)_ap_bootstrap_start + 0x10000); // XXX magic number
        printf("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        printf("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        printf("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        printf("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);                

        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);

        if (os_sinit_data->capabilities.rlp_wake_monitor) {
            printf("\nBSP: joining RLPs to MLE with MONITOR wakeup");
            printf("\nBSP: rlp_wakeup_addr = 0x%x", sinit_mle_data->rlp_wakeup_addr);
            *((uint32_t *)(unsigned long)(sinit_mle_data->rlp_wakeup_addr)) = 0x01;
        }else {
            printf("\nBSP: joining RLPs to MLE with GETSEC[WAKEUP]");
            __getsec_wakeup();
            printf("\nBSP: GETSEC[WAKEUP] completed");
        }
		
	} 
	
}

//---hvm_initialize_csrip-------------------------------------------------------
//vmx_initialize_vmcs_csrip
//initialize CS and RIP fields in the VMCS of the core
void vmx_initialize_vmcs_csrip(VCPU *vcpu, u16 cs_selector, u32 cs_base,
		u64 rip){

	vcpu->vmcs.guest_RIP = rip;
	vcpu->vmcs.guest_CS_selector = cs_selector; 
	vcpu->vmcs.guest_CS_base = cs_base; 
}

//---hvm_start------------------------------------------------------------------
//vmx_start_hvm
//start a HVM on the core
void vmx_start_hvm(VCPU *vcpu){
    printf("\nCPU(0x%02x): Starting HVM using CS:EIP=0x%04x:0x%08x...", vcpu->id,
			(u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
    _vmx_start_hvm(vcpu, __hva2spa__((void*)vcpu->vmx_vmcs_vaddr));
 		//we never get here, if we do, we just return and our caller is responsible
 		//for halting the core as something really bad happened!
}




//---do_quiesce-----------------------------------------------------------------
/*void vmx_do_quiesce(VCPU *vcpu){
        printf("\nCPU(0x%02x): got quiesce signal...", vcpu->id);
        //grab hold of quiesce lock
        spin_lock(&g_vmx_lock_quiesce);
        printf("\nCPU(0x%02x): grabbed quiesce lock.", vcpu->id);

        spin_lock(&g_vmx_lock_quiesce_counter);
        g_vmx_quiesce_counter=0;
        spin_unlock(&g_vmx_lock_quiesce_counter);
        
        //send all the other CPUs the quiesce signal
        g_vmx_quiesce=1;  //we are now processing quiesce
        _vmx_send_quiesce_signal(vcpu);
        
        //wait for all the remaining CPUs to quiesce
        printf("\nCPU(0x%02x): waiting for other CPUs to respond...", vcpu->id);
        while(g_vmx_quiesce_counter < (g_midtable_numentries-1) );
        printf("\nCPU(0x%02x): all CPUs quiesced successfully.", vcpu->id);
}*/

static void vmx_do_quiesce(VCPU *vcpu){
		printf("\n%s: REFACTORED, WE SHOULD NEVER BE HERE", __FUNCTION__);
		HALT();
	
}

static void vmx_do_wakeup(VCPU *vcpu){
		printf("\n%s: REFACTORED, WE SHOULD NEVER BE HERE", __FUNCTION__);
		HALT();
	
}


/* do_quiesce and do_wakeup should be called in pairs
 * the operations between do_quiesce and do_wakeup won't be influenced by other CPUs */
/*void vmx_do_wakeup(VCPU *vcpu){
        //set resume signal to resume the cores that are quiesced
        //Note: we do not need a spinlock for this since we are in any
        //case the only core active until this point
        g_vmx_quiesce_resume_counter=0;
        printf("\nCPU(0x%02x): waiting for other CPUs to resume...", vcpu->id);
        g_vmx_quiesce_resume_signal=1;
        
        while(g_vmx_quiesce_resume_counter < (g_midtable_numentries-1) );

        g_vmx_quiesce=0;  // we are out of quiesce at this point

        printf("\nCPU(0x%02x): all CPUs resumed successfully.", vcpu->id);
        
        //reset resume signal
        spin_lock(&g_vmx_lock_quiesce_resume_signal);
        g_vmx_quiesce_resume_signal=0;
        spin_unlock(&g_vmx_lock_quiesce_resume_signal);
                
        //release quiesce lock
        printf("\nCPU(0x%02x): releasing quiesce lock.", vcpu->id);
        spin_unlock(&g_vmx_lock_quiesce);
        
        //printf("\nCPU(0x%02x): Halting!", vcpu->id);
        //HALT();
}*/

//---setupvcpus-----------------------------------------------------------------
void vmx_setupvcpus(u32 cpu_vendor){
  u32 i;
  VCPU *vcpu;
  
	//ASSERT(midtable_numentries == 1);
	
  for(i=0; i < g_midtable_numentries; i++){
    //allocate VCPU structure
		vcpu = (VCPU *)((u32)g_vcpubuffers + (u32)(i * SIZE_STRUCT_VCPU));
    memset((void *)vcpu, 0, sizeof(VCPU));
    
    vcpu->cpu_vendor = cpu_vendor;
    
		//allocate runtime stack
    vcpu->esp = ((u32)g_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;    

    //allocate VMXON memory region
    vcpu->vmx_vmxonregion_vaddr = ((u32)g_vmx_vmxon_buffers + (i * PAGE_SIZE_4K)) ;
    memset((void *)vcpu->vmx_vmxonregion_vaddr, 0, PAGE_SIZE_4K);
    
		//allocate VMCS memory region
		vcpu->vmx_vmcs_vaddr = ((u32)g_vmx_vmcs_buffers + (i * PAGE_SIZE_4K)) ;
    memset((void *)vcpu->vmx_vmcs_vaddr, 0, PAGE_SIZE_4K);
		
		//allocate VMX IO bitmap region
		vcpu->vmx_vaddr_iobitmap = ((u32)g_vmx_iobitmap_buffers + (i * (2*PAGE_SIZE_4K))) ; 
		memset( (void *)vcpu->vmx_vaddr_iobitmap, 0, (2*PAGE_SIZE_4K));
		
		//allocate VMX guest and host MSR save areas
		vcpu->vmx_vaddr_msr_area_host = ((u32)g_vmx_msr_area_host_buffers + (i * (2*PAGE_SIZE_4K))) ; 
		memset( (void *)vcpu->vmx_vaddr_msr_area_host, 0, (2*PAGE_SIZE_4K));
		vcpu->vmx_vaddr_msr_area_guest = ((u32)g_vmx_msr_area_guest_buffers + (i * (2*PAGE_SIZE_4K))) ; 
		memset( (void *)vcpu->vmx_vaddr_msr_area_guest, 0, (2*PAGE_SIZE_4K));

		//allocate VMX MSR bitmap region
		vcpu->vmx_vaddr_msrbitmaps = ((u32)g_vmx_msrbitmap_buffers + (i * PAGE_SIZE_4K)) ; 
		memset( (void *)vcpu->vmx_vaddr_msrbitmaps, 0, PAGE_SIZE_4K);
		
		//allocate EPT paging structures
		#ifdef __NESTED_PAGING__		
		{
			vcpu->vmx_vaddr_ept_pml4_table = ((u32)g_vmx_ept_pml4_table_buffers + (i * PAGE_SIZE_4K));
			vcpu->vmx_vaddr_ept_pdp_table = ((u32)g_vmx_ept_pdp_table_buffers + (i * PAGE_SIZE_4K));  
			vcpu->vmx_vaddr_ept_pd_tables = ((u32)g_vmx_ept_pd_table_buffers + (i * (PAGE_SIZE_4K*4))); 		
			vcpu->vmx_vaddr_ept_p_tables = ((u32)g_vmx_ept_p_table_buffers + (i * (PAGE_SIZE_4K*2048))); 
		}
		#endif

		//allocate v86 monitor paging structures, GDT, IDT, LDT and TSS and stack
		//vcpu->v86m.vaddr_pagedir= ((u32)memregion_v86m_pagedir + (i * PAGE_SIZE_4K));
		//vcpu->v86m.vaddr_pagetables= ((u32)memregion_v86m_pagetables + (i * (1024*PAGE_SIZE_4K)));
		//vcpu->v86m.vaddr_idt=((u32)memregion_v86m_idt + (i * PAGE_SIZE_4K));
		//vcpu->v86m.vaddr_gdt=((u32)memregion_v86m_gdt+ (i * PAGE_SIZE_4K));
		//vcpu->v86m.vaddr_ldt=((u32)memregion_v86m_ldt + (i * PAGE_SIZE_4K));
		//vcpu->v86m.vaddr_tss=((u32)memregion_v86m_tss + (i * (4 * PAGE_SIZE_4K)));
		//vcpu->vaddr_v86m_ring0stack=((u32)memregion_v86m_ring0stack + (i * (4*PAGE_SIZE_4K)));		 

		//allocate limbo gdt and tss
		//vcpu->v86m.vaddr_limbo_gdt=((u32)memregion_limbo_gdt + (i * LIMBO_GDT_SIZE));
		//vcpu->v86m.vaddr_limbo_tss=((u32)memregion_limbo_tss + (i * LIMBO_TSS_SIZE));
		
		//other VCPU data such as LAPIC id, SIPI vector and receive indication
    vcpu->id = g_midtable[i].cpu_lapic_id;
    vcpu->idx = i;
    vcpu->sipivector = 0;
    vcpu->sipireceived = 0;

    g_midtable[i].vcpu_vaddr_ptr = (u32)vcpu;	//map LAPIC to VCPU in midtable
    
		//printf("\nCPU #%u: vcpu_vaddr_ptr=0x%08x, esp=0x%08x", i, midtable[i].vcpu_vaddr_ptr,
    //  vcpu->esp);
  }
}

static void vmx_apic_setup(VCPU *vcpu){
		printf("\n%s: REFACTORED, SHOULD NEVER BE HERE", __FUNCTION__);
		HALT();
	
}

//------------------------------------------------------------------------------
struct isolation_layer g_isolation_layer_vmx = {
	.initialize =	vmx_initialize,
	//.runtime_exception_handler = vmx_runtime_exception_handler,
	.isbsp = vmx_isbsp,
	.wakeup_aps = vmx_wakeup_aps,
	.hvm_initialize_csrip = vmx_initialize_vmcs_csrip,
	//.hvm_apic_setup = vmx_apic_setup,
	.hvm_start = vmx_start_hvm,
	.hvm_intercept_handler = emhf_parteventhub_intercept_handler_x86vmx,
	//.do_quiesce = vmx_do_quiesce,
	//.do_wakeup = vmx_do_wakeup,
	.setupvcpus = vmx_setupvcpus,
};



//==============================================================================
//VMX EMHF library interface implementation
static void _vmx_set_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] |= (1 << bit_offset);

  return;                        
}

static void __attribute__((unused)) _vmx_clear_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] &= ~(1 << bit_offset);

  return;
}

static u32 __attribute__((unused)) _vmx_test_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  if (bit_vector[byte_offset] & (1 << bit_offset))
    return 1;
  else 
    return 0;
}


//---IOPM Bitmap interface------------------------------------------------------
static void _vmx_lib_iopm_set_write(VCPU *vcpu, u32 port, u32 size){
  u32 i;
  for (i = 0; i < size; i ++)
    _vmx_set_page_prot((port+i), (u8 *)vcpu->vmx_vaddr_iobitmap);
}

//---MSRPM Bitmap interface------------------------------------------------------
static void _vmx_lib_msrpm_set_write(VCPU __attribute__((unused)) *vcpu, u32 __attribute__((unused)) msr){
  return;
}

//---hardware pagetable flush-all routine---------------------------------------
static void _vmx_lib_hwpgtbl_flushall(VCPU *vcpu){
  __vmx_invept(VMX_EPT_SINGLE_CONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full, 
          0);
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}

//---hardware pagetable protection manipulation routine-------------------------
static void _vmx_lib_hwpgtbl_setprot(VCPU *vcpu, u64 gpa, u64 flags){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;

  pt[pfn] &= ~(u64)7; //clear all previous flags
  pt[pfn] |= flags; //set new flags

	//flush TLB
	_vmx_lib_hwpgtbl_flushall(vcpu);
}

static void __attribute__((unused)) _vmx_lib_hwpgtbl_setentry(VCPU *vcpu, u64 gpa, u64 value){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;

  pt[pfn] = value; //set new value

  //flush the EPT mappings for changes to take effect
	_vmx_lib_hwpgtbl_flushall(vcpu);
}

static u64 _vmx_lib_hwpgtbl_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;

  return (pt[pfn] & (u64)7) ;
}

//---guest page-table walker, returns guest physical address--------------------
//note: returns 0xFFFFFFFF if there is no mapping
u8 * _vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr){

  if((u32)vcpu->vmcs.guest_CR4 & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)vcpu->vmcs.guest_CR3;
    u32 pdpt_index, pd_index, pt_index, offset;
    u64 paddr;
    pdpt_t kpdpt;
    pdt_t kpd; 
    pt_t kpt; 
    u32 pdpt_entry, pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pdpt_index = pae_get_pdpt_index(vaddr);
    pd_index = pae_get_pdt_index(vaddr);
    pt_index = pae_get_pt_index(vaddr);
    offset = pae_get_offset_4K_page(vaddr);  

    //grab pdpt entry
    tmp = pae_get_addr_from_32bit_cr3(kcr3);
    kpdpt = (pdpt_t)((u32)tmp); 
    pdpt_entry = kpdpt[pdpt_index];
  
    //grab pd entry
    tmp = pae_get_addr_from_pdpe(pdpt_entry);
    kpd = (pdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)pae_get_addr_from_pde(pd_entry);
      kpt = (pt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      // find physical page base addr from page table entry 
      paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 2MB page 
      offset = pae_get_offset_big(vaddr);
      paddr = (u64)pae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u8 *)(u32)paddr;
    
  }else{
    //non-PAE 2 level paging used by guest
    u32 kcr3 = (u32)vcpu->vmcs.guest_CR3;
    u32 pd_index, pt_index, offset;
    u64 paddr;
    npdt_t kpd; 
    npt_t kpt; 
    u32 pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pd_index = npae_get_pdt_index(vaddr);
    pt_index = npae_get_pt_index(vaddr);
    offset = npae_get_offset_4K_page(vaddr);  
  
    // grab pd entry
    tmp = npae_get_addr_from_32bit_cr3(kcr3);
    kpd = (npdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];
  
    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)npae_get_addr_from_pde(pd_entry);
      kpt = (npt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      // find physical page base addr from page table entry 
      paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 4MB page 
      offset = npae_get_offset_big(vaddr);
      paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u8 *)(u32)paddr;
  }
}


//---reboot functionality-------------------------------------------------------
static void _vmx_lib_reboot(VCPU __attribute__((unused)) *vcpu){

    printf("\nHello from _vmx_lib_reboot\n");
    if(txt_is_launched()) {
        printf("\nI detect that we are in a TXT environment.  Doing special TXT reboot\n");
    }

	//step-1: shut VMX off, else CPU ignores INIT signal!
	__asm__ __volatile__("vmxoff \r\n");
	write_cr4(read_cr4() & ~(CR4_VMXE));
	
	//step-2: zero out IDT
	emhf_xcphandler_resetIDT();
	
	//step-3: execute ud2 instruction to generate triple fault
	__asm__ __volatile__("ud2 \r\n");
	
	//never get here
	printf("\n%s: should never get here. halt!", __FUNCTION__);
	HALT();
}


struct emhf_library g_emhf_library_vmx = {
	.emhf_iopm_set_write = _vmx_lib_iopm_set_write,
	.emhf_msrpm_set_write = _vmx_lib_msrpm_set_write,
	.emhf_hwpgtbl_flushall = _vmx_lib_hwpgtbl_flushall,
	.emhf_hwpgtbl_setprot = _vmx_lib_hwpgtbl_setprot,
	.emhf_hwpgtbl_getprot = _vmx_lib_hwpgtbl_getprot,
	.emhf_guestpgtbl_walk = _vmx_lib_guestpgtbl_walk,
	.emhf_reboot = _vmx_lib_reboot,
};



