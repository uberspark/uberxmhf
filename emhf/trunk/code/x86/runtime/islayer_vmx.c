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

#include <target.h>
#include <globals.h>
#include <txt.h>

//==============================================================================
// static (local) data
//==============================================================================



//==============================================================================
// static (local) function definitions
//==============================================================================
static void _vmx_lib_reboot(VCPU *vcpu);
static u8 *_vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);

//---initVT: initializes CPU VT-------------------------------------------------
static void _vmx_initVT(VCPU *vcpu){
	//step-0: to enable VMX on a core, we require it to have a TR loaded,
	//so load it for this core
	__vmx_loadTR();


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
	  	u64 vmxonregion_paddr = __hva2spa__(vcpu->vmx_vmxonregion_vaddr);
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
}

//---NMI processing routine-----------------------------------------------------
static void _vmx_processNMI(VCPU *vcpu, struct regs *r){
  
	if( (!vcpu->nmiinhvm) && (!g_vmx_quiesce) ){
    printf("\nCPU(0x%02x): Spurious NMI within hypervisor. halt!", vcpu->id);
    HALT();
  }

	if(g_vmx_quiesce){
    //ok this NMI is because of g_vmx_quiesce. note: g_vmx_quiesce can be 1 and
    //this could be a NMI for the guest. we have no way of distinguising
    //this. however, since g_vmx_quiesce=1, we can handle this NMI as a quiesce NMI
    //and rely on the platform h/w to reissue the NMI later
    printf("\nCPU(0x%02x): NMI for core quiesce", vcpu->id);
    printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x", vcpu->id, (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
  
    printf("\nCPU(0x%02x): quiesced, updating counter. awaiting EOQ...", vcpu->id);
    spin_lock(&g_vmx_lock_quiesce_counter);
    g_vmx_quiesce_counter++;
    spin_unlock(&g_vmx_lock_quiesce_counter);
    
    while(!g_vmx_quiesce_resume_signal);
    printf("\nCPU(0x%02x): EOQ received, resuming...", vcpu->id);
    
    spin_lock(&g_vmx_lock_quiesce_resume_counter);
    g_vmx_quiesce_resume_counter++;
    spin_unlock(&g_vmx_lock_quiesce_resume_counter);
    
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


//---putVMCS--------------------------------------------------------------------
// routine takes vcpu vmcsfields and stores it in the CPU VMCS 
static void _vmx_putVMCS(VCPU *vcpu){
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
static void _vmx_getVMCS(VCPU *vcpu){
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
static void _vmx_dumpVMCS(VCPU *vcpu){
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
    __vmx_start_hvm();
    printf("\nCPU(0x%02x): Error in VMLAUNCH. HALT!");
    HALT();
  }

  HALT();
}


//---quiescing implementation---------------------------------------------------
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
}


//---intercept handler (I/O port access)----------------------------------------
static void _vmx_handle_intercept_ioportaccess(VCPU *vcpu, struct regs *r){
  u32 access_size, access_type, portnum, stringio;
	u32 app_ret_status = APP_IOINTERCEPT_CHAIN;
	
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

//---intercept handler (EPT voilation)------------------------------------------
static void _vmx_handle_intercept_eptviolation(VCPU *vcpu, struct regs *r){
  u32 errorcode, gpa, gva;
	errorcode = (u32)vcpu->vmcs.info_exit_qualification;
	gpa = (u32) vcpu->vmcs.guest_paddr_full;
	gva = (u32) vcpu->vmcs.info_guest_linear_address;

	//check if EPT violation is due to LAPIC interception
	if(vmx_isbsp() && (gpa >= g_vmx_lapic_base) && (gpa < (g_vmx_lapic_base + PAGE_SIZE_4K)) ){
    vmx_lapic_access_handler(vcpu, gpa, errorcode);
  }else{ //no, pass it to emhf app  
	  emhf_app_handleintercept_hwpgtblviolation(vcpu, r, gpa, gva,
  	  (errorcode & 7));
	}		
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
//
//VMX is very picky with MTRR/PAT configuration within EPTs, we have to make
//sure that guest MTRR writes go to its local copy. Technically we will have
//to propagate the writes to the actual MTRRs and update EPTs accordingly, but
//both Linux and Windows do not change default caching policies set by the BIOS
//so for now we are good just accessing local values for read and writes
//------------------------------------------------------------------------------
  
//---intercept handler (WRMSR)--------------------------------------------------
static void _vmx_handle_intercept_wrmsr(VCPU *vcpu, struct regs *r){
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
		case IA32_MTRRCAP: 					vcpu->vmx_guestmtrrmsrs[0].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[0].lodword= r->eax;  break;
		case IA32_MTRR_DEF_TYPE: 		vcpu->vmx_guestmtrrmsrs[1].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[1].lodword= r->eax;  break;  
		case IA32_MTRR_FIX64K_00000:vcpu->vmx_guestmtrrmsrs[2].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[2].lodword= r->eax;  break;
		case IA32_MTRR_FIX16K_80000:vcpu->vmx_guestmtrrmsrs[3].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[3].lodword= r->eax;  break;	
		case IA32_MTRR_FIX16K_A0000:vcpu->vmx_guestmtrrmsrs[4].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[4].lodword= r->eax;  break;	
		case IA32_MTRR_FIX4K_C0000:	vcpu->vmx_guestmtrrmsrs[5].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[5].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_C8000:	vcpu->vmx_guestmtrrmsrs[6].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[6].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_D0000:	vcpu->vmx_guestmtrrmsrs[7].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[7].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_D8000:	vcpu->vmx_guestmtrrmsrs[8].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[8].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_E0000:	vcpu->vmx_guestmtrrmsrs[9].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[9].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_E8000:	vcpu->vmx_guestmtrrmsrs[10].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[10].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_F0000:	vcpu->vmx_guestmtrrmsrs[11].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[11].lodword= r->eax;  break;		
		case IA32_MTRR_FIX4K_F8000:	vcpu->vmx_guestmtrrmsrs[12].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[12].lodword= r->eax;  break;		
		case IA32_MTRR_PHYSBASE0:		vcpu->vmx_guestmtrrmsrs[13].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[13].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK0:		vcpu->vmx_guestmtrrmsrs[14].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[14].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE1:		vcpu->vmx_guestmtrrmsrs[15].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[15].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK1:		vcpu->vmx_guestmtrrmsrs[16].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[16].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE2:		vcpu->vmx_guestmtrrmsrs[17].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[17].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK2:		vcpu->vmx_guestmtrrmsrs[18].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[18].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE3:		vcpu->vmx_guestmtrrmsrs[19].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[19].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK3:		vcpu->vmx_guestmtrrmsrs[20].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[20].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE4:		vcpu->vmx_guestmtrrmsrs[21].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[21].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK4:		vcpu->vmx_guestmtrrmsrs[22].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[22].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE5:		vcpu->vmx_guestmtrrmsrs[23].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[23].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK5:		vcpu->vmx_guestmtrrmsrs[24].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[24].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE6:		vcpu->vmx_guestmtrrmsrs[25].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[25].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK6:		vcpu->vmx_guestmtrrmsrs[26].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[26].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSBASE7:		vcpu->vmx_guestmtrrmsrs[27].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[27].lodword= r->eax;  break;			
		case IA32_MTRR_PHYSMASK7:		vcpu->vmx_guestmtrrmsrs[28].hidword= r->edx;  vcpu->vmx_guestmtrrmsrs[28].lodword= r->eax;  break;	

		default:{
			asm volatile ("wrmsr\r\n"
          : //no outputs
          :"a"(r->eax), "c" (r->ecx), "d" (r->edx));	
			break;
		}
	}
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	//printf("\nCPU(0x%02x): WRMSR end", vcpu->id);

}

//---intercept handler (RDMSR)--------------------------------------------------
static void _vmx_handle_intercept_rdmsr(VCPU *vcpu, struct regs *r){
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
		case IA32_MTRRCAP: 					r->edx = vcpu->vmx_guestmtrrmsrs[0].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[0].lodword;  break;
		case IA32_MTRR_DEF_TYPE: 		r->edx = vcpu->vmx_guestmtrrmsrs[1].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[1].lodword;  break;  
		case IA32_MTRR_FIX64K_00000:r->edx = vcpu->vmx_guestmtrrmsrs[2].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[2].lodword;  break;
		case IA32_MTRR_FIX16K_80000:r->edx = vcpu->vmx_guestmtrrmsrs[3].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[3].lodword;  break;	
		case IA32_MTRR_FIX16K_A0000:r->edx = vcpu->vmx_guestmtrrmsrs[4].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[4].lodword;  break;	
		case IA32_MTRR_FIX4K_C0000:	r->edx = vcpu->vmx_guestmtrrmsrs[5].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[5].lodword;  break;		
		case IA32_MTRR_FIX4K_C8000:	r->edx = vcpu->vmx_guestmtrrmsrs[6].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[6].lodword;  break;		
		case IA32_MTRR_FIX4K_D0000:	r->edx = vcpu->vmx_guestmtrrmsrs[7].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[7].lodword;  break;		
		case IA32_MTRR_FIX4K_D8000:	r->edx = vcpu->vmx_guestmtrrmsrs[8].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[8].lodword;  break;		
		case IA32_MTRR_FIX4K_E0000:	r->edx = vcpu->vmx_guestmtrrmsrs[9].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[9].lodword;  break;		
		case IA32_MTRR_FIX4K_E8000:	r->edx = vcpu->vmx_guestmtrrmsrs[10].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[10].lodword;  break;		
		case IA32_MTRR_FIX4K_F0000:	r->edx = vcpu->vmx_guestmtrrmsrs[11].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[11].lodword;  break;		
		case IA32_MTRR_FIX4K_F8000:	r->edx = vcpu->vmx_guestmtrrmsrs[12].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[12].lodword;  break;		
		case IA32_MTRR_PHYSBASE0:		r->edx = vcpu->vmx_guestmtrrmsrs[13].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[13].lodword;  break;			
		case IA32_MTRR_PHYSMASK0:		r->edx = vcpu->vmx_guestmtrrmsrs[14].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[14].lodword;  break;			
		case IA32_MTRR_PHYSBASE1:		r->edx = vcpu->vmx_guestmtrrmsrs[15].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[15].lodword;  break;			
		case IA32_MTRR_PHYSMASK1:		r->edx = vcpu->vmx_guestmtrrmsrs[16].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[16].lodword;  break;			
		case IA32_MTRR_PHYSBASE2:		r->edx = vcpu->vmx_guestmtrrmsrs[17].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[17].lodword;  break;			
		case IA32_MTRR_PHYSMASK2:		r->edx = vcpu->vmx_guestmtrrmsrs[18].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[18].lodword;  break;			
		case IA32_MTRR_PHYSBASE3:		r->edx = vcpu->vmx_guestmtrrmsrs[19].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[19].lodword;  break;			
		case IA32_MTRR_PHYSMASK3:		r->edx = vcpu->vmx_guestmtrrmsrs[20].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[20].lodword;  break;			
		case IA32_MTRR_PHYSBASE4:		r->edx = vcpu->vmx_guestmtrrmsrs[21].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[21].lodword;  break;			
		case IA32_MTRR_PHYSMASK4:		r->edx = vcpu->vmx_guestmtrrmsrs[22].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[22].lodword;  break;			
		case IA32_MTRR_PHYSBASE5:		r->edx = vcpu->vmx_guestmtrrmsrs[23].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[23].lodword;  break;			
		case IA32_MTRR_PHYSMASK5:		r->edx = vcpu->vmx_guestmtrrmsrs[24].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[24].lodword;  break;			
		case IA32_MTRR_PHYSBASE6:		r->edx = vcpu->vmx_guestmtrrmsrs[25].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[25].lodword;  break;			
		case IA32_MTRR_PHYSMASK6:		r->edx = vcpu->vmx_guestmtrrmsrs[26].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[26].lodword;  break;			
		case IA32_MTRR_PHYSBASE7:		r->edx = vcpu->vmx_guestmtrrmsrs[27].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[27].lodword;  break;			
		case IA32_MTRR_PHYSMASK7:		r->edx = vcpu->vmx_guestmtrrmsrs[28].hidword;  r->eax = vcpu->vmx_guestmtrrmsrs[28].lodword;  break;	


/*    case IA32_MTRRCAP: 					
		case IA32_MTRR_DEF_TYPE: 		  
		case IA32_MTRR_FIX64K_00000:
		case IA32_MTRR_FIX16K_80000:	
		case IA32_MTRR_FIX16K_A0000:	
		case IA32_MTRR_FIX4K_C0000:			
		case IA32_MTRR_FIX4K_C8000:			
		case IA32_MTRR_FIX4K_D0000:			
		case IA32_MTRR_FIX4K_D8000:			
		case IA32_MTRR_FIX4K_E0000:			
		case IA32_MTRR_FIX4K_E8000:			
		case IA32_MTRR_FIX4K_F0000:			
		case IA32_MTRR_FIX4K_F8000:			
		case IA32_MTRR_PHYSBASE0:					
		case IA32_MTRR_PHYSMASK0:					
		case IA32_MTRR_PHYSBASE1:					
		case IA32_MTRR_PHYSMASK1:					
		case IA32_MTRR_PHYSBASE2:					
		case IA32_MTRR_PHYSMASK2:					
		case IA32_MTRR_PHYSBASE3:					
		case IA32_MTRR_PHYSMASK3:					
		case IA32_MTRR_PHYSBASE4:					
		case IA32_MTRR_PHYSMASK4:					
		case IA32_MTRR_PHYSBASE5:					
		case IA32_MTRR_PHYSMASK5:					
		case IA32_MTRR_PHYSBASE6:					
		case IA32_MTRR_PHYSMASK6:					
		case IA32_MTRR_PHYSBASE7:					
		case IA32_MTRR_PHYSMASK7:			
			_vmx_lib_reboot(vcpu);
			//we never get here
			printf("\nCPU(0x%02x): halting on RDMSR!");
			HALT();
	*/
		default:{
			asm volatile ("rdmsr\r\n"
          : "=a"(r->eax), "=d"(r->edx)
          : "c" (r->ecx));
			break;
		}
	}
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	//printf("\nCPU(0x%02x): RDMSR (0x%08x)=0x%08x%08x", vcpu->id, r->ecx, r->edx, r->eax);

}

//---intercept handler (CPUID)--------------------------------------------------
static void _vmx_handle_intercept_cpuid(VCPU *vcpu, struct regs *r){
	//printf("\nCPU(0x%02x): CPUID", vcpu->id);
	asm volatile ("cpuid\r\n"
          :"=a"(r->eax), "=b"(r->ebx), "=c"(r->ecx), "=d"(r->edx)
          :"a"(r->eax), "c" (r->ecx));
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}


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

//---vmx int 15 intercept handler-----------------------------------------------
static void _vmx_int15_handleintercept(VCPU *vcpu, struct regs *r){
	u16 cs, ip;
	u8 *bdamemory = (u8 *)0x4AC;
	
	//printf("\nCPU(0x%02x): BDA dump in intercept: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
	//		bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
	//			bdamemory[5], bdamemory[6], bdamemory[7]);

	//if in V86 mode translate the virtual address to physical address
	if( (vcpu->vmcs.guest_CR0 & CR0_PE) && (vcpu->vmcs.guest_CR0 & CR0_PG) &&
			(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM) ){
		u8 *bdamemoryphysical;
		bdamemoryphysical = (u8 *)_vmx_lib_guestpgtbl_walk(vcpu, (u32)bdamemory);
		ASSERT( (u32)bdamemoryphysical != 0xFFFFFFFFUL );
		printf("\nINT15 (E820): V86 mode, bdamemory translated from %08x to %08x",
			(u32)bdamemory, (u32)bdamemoryphysical);
		bdamemory = bdamemoryphysical; 		
	}
	
	//if E820 service then...
	if((u16)r->eax == 0xE820){
		//AX=0xE820, EBX=continuation value, 0 for first call
		//ES:DI pointer to buffer, ECX=buffer size, EDX='SMAP'
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
		printf("\nCPU(0x%02x): INT 15(e820): AX=0x%04x, EDX=0x%08x, EBX=0x%08x, ECX=0x%08x, ES=0x%04x, DI=0x%04x", vcpu->id, 
		(u16)r->eax, r->edx, r->ebx, r->ecx, (u16)vcpu->vmcs.guest_ES_selector, (u16)r->edi);
		
		ASSERT(r->edx == 0x534D4150UL);  //'SMAP' should be specified by guest
		ASSERT(r->ebx < rpb->XtVmmE820NumEntries); //invalid continuation value specified by guest!
			
		//copy the e820 descriptor and return its size in ECX
		memcpy((void *)((u32)((vcpu->vmcs.guest_ES_base)+(u16)r->edi)), (void *)&g_e820map[r->ebx],
					sizeof(GRUBE820));
		r->ecx=20;

		//set EAX to 'SMAP' as required by the service call				
		r->eax=r->edx;

		//we need to update carry flag in the guest EFLAGS register
		//however since INT 15 would have pushed the guest FLAGS on stack
		//we cannot simply reflect the change by modifying vcpu->vmcs.guest_RFLAGS.
		//instead we need to make the change to the pushed FLAGS register on
		//the guest stack. the real-mode IRET frame looks like the following 
		//when viewed at top of stack
		//guest_ip		(16-bits)
		//guest_cs		(16-bits)
		//guest_flags (16-bits)
		//...
		
		{
			u16 guest_cs, guest_ip, guest_flags;
			u16 *gueststackregion = (u16 *)( (u32)vcpu->vmcs.guest_SS_base + (u16)vcpu->vmcs.guest_RSP );
		
		
			//if V86 mode translate the virtual address to physical address
			if( (vcpu->vmcs.guest_CR0 & CR0_PE) && (vcpu->vmcs.guest_CR0 & CR0_PG) &&
					(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM) ){
				u8 *gueststackregionphysical = (u8 *)_vmx_lib_guestpgtbl_walk(vcpu, (u32)gueststackregion);
				ASSERT( (u32)gueststackregionphysical != 0xFFFFFFFFUL );
				printf("\nINT15 (E820): V86 mode, gueststackregion translated from %08x to %08x",
					(u32)gueststackregion, (u32)gueststackregionphysical);
				gueststackregion = (u16 *)gueststackregionphysical; 		
			}
		
			
			//printf("\nINT15 (E820): guest_ss=%04x, sp=%04x, stackregion=%08x", (u16)vcpu->vmcs.guest_SS_selector,
			//		(u16)vcpu->vmcs.guest_RSP, (u32)gueststackregion);
			
			//get guest IP, CS and FLAGS from the IRET frame
			guest_ip = gueststackregion[0];
			guest_cs = gueststackregion[1];
			guest_flags = gueststackregion[2];

			//printf("\nINT15 (E820): guest_flags=%04x, guest_cs=%04x, guest_ip=%04x",
			//	guest_flags, guest_cs, guest_ip);
		
			//increment e820 descriptor continuation value
			r->ebx=r->ebx+1;
					
			if(r->ebx > (rpb->XtVmmE820NumEntries-1) ){
				//we have reached the last record, so set CF and make EBX=0
				r->ebx=0;
				guest_flags |= (u16)EFLAGS_CF;
				gueststackregion[2] = guest_flags;
			}else{
				//we still have more records, so clear CF
				guest_flags &= ~(u16)EFLAGS_CF;
				gueststackregion[2] = guest_flags;
			}
		  
		}

 	  //update RIP to execute the IRET following the VMCALL instruction
 	  //effectively returning from the INT 15 call made by the guest
	  vcpu->vmcs.guest_RIP += 3;

		return;
	}
	
	
	//ok, this is some other INT 15h service, so simply chain to the original
	//INT 15h handler
	
	//get IP and CS of the original INT 15h handler
	ip = *((u16 *)((u32)bdamemory + 4));
	cs = *((u16 *)((u32)bdamemory + 6));
	
	//printf("\nCPU(0x%02x): INT 15, transferring control to 0x%04x:0x%04x", vcpu->id,
	//	cs, ip);
		
	//update VMCS with the CS and IP and let go
	vcpu->vmcs.guest_RIP = ip;
	vcpu->vmcs.guest_CS_base = cs * 16;
	vcpu->vmcs.guest_CS_selector = cs;		 
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

//---generic exception handler--------------------------------------------------
void vmx_runtime_exception_handler(u32 vector, struct regs *r){
	VCPU *vcpu = _vmx_getvcpu();
  INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *noecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *)((u32)r->esp + (u32)0x0C);
  INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *ecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *)((u32)r->esp + (u32)0x0C);

  printf("\nCPU(0x%02x): %s excp=0x%08x", vcpu->id, __FUNCTION__, vector);
  printf("\nCPU(0x%02x): %s ESP=0x%08x", vcpu->id, __FUNCTION__, r->esp);
  
	if(vector == NMI_VECTOR){
    _vmx_processNMI(vcpu, r);
    return;
  }	
}


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
    } /* else we need to do Intel TXT wakeup. */
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
    _vmx_start_hvm(vcpu, __hva2spa__(vcpu->vmx_vmcs_vaddr));
 		//we never get here, if we do, we just return and our caller is responsible
 		//for halting the core as something really bad happened!
}


//---hvm_intercept_handler------------------------------------------------------
u32 vmx_intercept_handler(VCPU *vcpu, struct regs *r){
  //read VMCS from physical CPU/core
	_vmx_getVMCS(vcpu);

	//sanity check for VM-entry errors
	if( (u32)vcpu->vmcs.info_vmexit_reason & 0x80000000UL ){
		printf("\nVM-ENTRY error: reason=0x%08x, qualification=0x%016llx", 
			(u32)vcpu->vmcs.info_vmexit_reason, (u64)vcpu->vmcs.info_exit_qualification);
    _vmx_dumpVMCS(vcpu);
    HALT();
  }
  
  //handle intercepts
  switch((u32)vcpu->vmcs.info_vmexit_reason){
		case VMEXIT_IOIO:
			{
				_vmx_handle_intercept_ioportaccess(vcpu, r);
			}
			break;

      case VMEXIT_EPT_VIOLATION:{
		    _vmx_handle_intercept_eptviolation(vcpu, r);
    	}
			break;  	

    case VMEXIT_HLT:
			if(!vcpu->vmx_guest_unrestricted){
				//isl_handleintercept_hlt(vcpu, r);
				printf("\nCPU(0x%02x): V86 monitor based real-mode exec. unsupported!", vcpu->id);
				HALT();
			}else{
			 	printf("\nCPU(0x%02x): Unexpected HLT intercept in UG, Halting!", vcpu->id);
				HALT();
			}
			break;

 		case VMEXIT_EXCEPTION:{
			switch( ((u32)vcpu->vmcs.info_vmexit_interrupt_information & INTR_INFO_VECTOR_MASK) ){
				//case 0x0D: //v86monitor only
				//	_vmx_handle_intercept_exception_0D(vcpu, r);
				//	break;

				case 0x01:
					vmx_lapic_access_dbexception(vcpu, r);
					break;				
				
				case 0x02:	//NMI
					vcpu->nmiinhvm=1;	//this NMI occured when the core was in guest (HVM)
					_vmx_processNMI(vcpu, r);
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
				//case 0x3: //CR3 access (v86monitor only)
				//	_vmx_handle_intercept_cr3access(vcpu, r, gpr, tofrom);
				//	break;
				
				case 0x4: //CR4 access
					if(!vcpu->vmx_guest_unrestricted){
						printf("\nHALT: v86 monitor based real-mode exec. unsupported!");
						HALT();
						//handle_intercept_cr4access(vcpu, r, gpr, tofrom);
					}else{
						vmx_handle_intercept_cr4access_ug(vcpu, r, gpr, tofrom);	
					}
					break;
				
				//case 0x0: //CR0 access (v86monitor only)
				//	_vmx_handle_intercept_cr0access(vcpu, r, gpr, tofrom);
				//	break;
			
				default:
					printf("\nunhandled crx, halting!");
					HALT();
			}
			vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
		}
		break;	

 		case VMEXIT_RDMSR:
			_vmx_handle_intercept_rdmsr(vcpu, r);
			break;
			
		case VMEXIT_WRMSR:
			_vmx_handle_intercept_wrmsr(vcpu, r);
			break;
			
		case VMEXIT_CPUID:
			_vmx_handle_intercept_cpuid(vcpu, r);
			break;

    case VMEXIT_INIT:{
      emhf_app_handleshutdown(vcpu, r);      
      printf("\nCPU(0x%02x): warning, emhf_app_handleshutdown returned!", vcpu->id);
      HALT();
    }
    break;

    case VMEXIT_VMCALL:{
			//check to see if this is a hypercall for INT 15h hooking
			if(vcpu->vmcs.guest_CS_base == (VMX_UG_E820HOOK_CS << 4) &&
				vcpu->vmcs.guest_RIP == VMX_UG_E820HOOK_IP){
				//assertions, we need to be either in real-mode or in protected
				//mode with paging and EFLAGS.VM bit set (virtual-8086 mode)
				ASSERT( !(vcpu->vmcs.guest_CR0 & CR0_PE)  ||
					( (vcpu->vmcs.guest_CR0 & CR0_PE) && (vcpu->vmcs.guest_CR0 & CR0_PG) &&
						(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM)  ) );
				_vmx_int15_handleintercept(vcpu, r);	
			}else{	//if not E820 hook, give app a chance to handle the hypercall
				if( emhf_app_handlehypercall(vcpu, r) != APP_SUCCESS){
					printf("\nCPU(0x%02x): error(halt), unhandled hypercall 0x%08x!", vcpu->id, r->eax);
					HALT();
				}
      	vcpu->vmcs.guest_RIP += 3;
			}
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
  _vmx_putVMCS(vcpu);
  if(vcpu->vmcs.guest_RIP == 0x7c00){
		printf("\nCPU(0x%02x): We are starting at guest boot-sector...", vcpu->id);
	}
	
	return 1;
}


//---do_quiesce-----------------------------------------------------------------
void vmx_do_quiesce(VCPU *vcpu){
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
        
        //perform operation now with all CPUs halted...
        
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
}

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
    vcpu->sipivector = 0;
    vcpu->sipireceived = 0;

    g_midtable[i].vcpu_vaddr_ptr = (u32)vcpu;	//map LAPIC to VCPU in midtable
    
		//printf("\nCPU #%u: vcpu_vaddr_ptr=0x%08x, esp=0x%08x", i, midtable[i].vcpu_vaddr_ptr,
    //  vcpu->esp);
  }
}



//------------------------------------------------------------------------------
struct isolation_layer g_isolation_layer_vmx = {
	.initialize =	vmx_initialize,
	.runtime_exception_handler = vmx_runtime_exception_handler,
	.isbsp = vmx_isbsp,
	.wakeup_aps = vmx_wakeup_aps,
	.hvm_initialize_csrip = vmx_initialize_vmcs_csrip,
	.hvm_apic_setup = vmx_apic_setup,
	.hvm_start = vmx_start_hvm,
	.hvm_intercept_handler = vmx_intercept_handler,
	.do_quiesce = vmx_do_quiesce,
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

static void _vmx_clear_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] &= ~(1 << bit_offset);

  return;
}

static u32 _vmx_test_page_prot(u32 pfn, u8 *bit_vector){
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
static void _vmx_lib_msrpm_set_write(VCPU *vcpu, u32 msr){
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

static void _vmx_lib_hwpgtbl_setentry(VCPU *vcpu, u64 gpa, u64 value){
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
static u8 * _vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr){

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
static void _vmx_lib_reboot(VCPU *vcpu){

	//step-1: shut VMX off, else CPU ignores INIT signal!
	__asm__ __volatile__("vmxoff \r\n");
	write_cr4(read_cr4() & ~(CR4_VMXE));
	
	//step-2: zero out IDT
	{
		extern u32 x_idt_start[];
		memset((void *)x_idt_start, 0, SIZE_RUNTIME_IDT);
	}
	
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



