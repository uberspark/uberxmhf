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
 * EMHF partition component interface (x86 SVM backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//---init SVM-------------------------------------------------------------------
static void _svm_initSVM(VCPU *vcpu){
  u32 eax, edx, ecx, ebx;
  u64 hsave_pa;

  //check if CPU supports SVM extensions 
  cpuid(0x80000001, &eax, &ebx, &ecx, &edx);
  if( !(ecx & (1<<ECX_SVM)) ){
   printf("\nCPU(0x%02x): no SVM extensions. HALT!", vcpu->id);
   HALT();
  }
  
  //check if SVM extensions are disabled by the BIOS 
  rdmsr(VM_CR_MSR, &eax, &edx);
  if( eax & (1<<VM_CR_SVME_DISABLE) ){
    printf("\nCPU(0x%02x): SVM extensions disabled in the BIOS. HALT!", vcpu->id);
    HALT();
  }

  // check for nested paging support and number of ASIDs 
	cpuid(0x8000000A, &eax, &ebx, &ecx, &edx);
  if(!(edx & 0x1)){
      printf("\nCPU(0x%02x): No support for Nested Paging, HALTING!", vcpu->id);
		HALT();
	}
	
  printf("\nCPU(0x%02x): Nested paging support present", vcpu->id);
	if( (ebx-1) < 2 ){
		printf("\nCPU(0x%02x): Total number of ASID is too low, HALTING!", vcpu->id);
		HALT();
	}
	
	printf("\nCPU(0x%02x): Total ASID is valid", vcpu->id);

  // enable SVM and debugging support (if required)   
  rdmsr((u32)VM_CR_MSR, &eax, &edx);
  eax &= (~(1<<VM_CR_DPD));
  wrmsr((u32)VM_CR_MSR, eax, edx);
  printf("\nCPU(0x%02x): HDT debugging enabled", vcpu->id);

  rdmsr((u32)MSR_EFER, &eax, &edx);
  eax |= (1<<EFER_SVME);
  wrmsr((u32)MSR_EFER, eax, edx);
  printf("\nCPU(0x%02x): SVM extensions enabled", vcpu->id);

  // Initialize the HSA 
  //printf("\nHSAVE area=0x%08X", vcpu->hsave_vaddr_ptr);
  hsave_pa = hva2spa((void*)vcpu->hsave_vaddr_ptr);
  //printf("\nHSAVE physaddr=0x%08x", hsave_pa);
  eax = (u32)hsave_pa;
  edx = (u32)(hsave_pa >> 32);
  wrmsr((u32)VM_HSAVE_PA, eax, edx);
  printf("\nCPU(0x%02x): SVM HSAVE initialized", vcpu->id);

  // enable NX protections 
  rdmsr(MSR_EFER, &eax, &edx);
  eax |= (1 << EFER_NXE);
  wrmsr(MSR_EFER, eax, edx);
  printf("\nCPU(0x%02x): NX protection enabled", vcpu->id);

  return;
}


//---svm int 15 hook enabling function------------------------------------------
static void	_svm_int15_initializehook(VCPU *vcpu){
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

		//implant VMMCALL followed by IRET at 0040:04AC
		bdamemory[0]= 0x0f;	//VMMCALL						
		bdamemory[1]= 0x01;
		bdamemory[2]= 0xd9;																	
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


//---setup VMCB-----------------------------------------------------------------
static void _svm_initVMCB(VCPU *vcpu){
  
  struct _svm_vmcbfields *vmcb = (struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr;
  
  printf("\nCPU(0x%02x): VMCB at 0x%08x", vcpu->id, (u32)vmcb);
  memset(vmcb, 0, sizeof(struct _svm_vmcbfields));
  
  // set up CS descr 
  vmcb->cs.selector = 0x0;
  vmcb->cs.base = 0x0;
  vmcb->cs.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->cs.attrib = 0x009b;
  
  // set up DS descr 
  vmcb->ds.selector = 0x0;
  vmcb->ds.base = 0x0;
  vmcb->ds.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->ds.attrib = 0x0093; // read/write 
  
  // set up ES descr 
  vmcb->es.selector = 0x0;
  vmcb->es.base = 0x0;
  vmcb->es.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->es.attrib = 0x0093; // read/write 

  // set up FS descr 
  vmcb->fs.selector = 0x0;
  vmcb->fs.base = 0x0;
  vmcb->fs.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->fs.attrib = 0x0093; // read/write 

  // set up GS descr 
  vmcb->gs.selector = 0x0;
  vmcb->gs.base = 0x0;
  vmcb->gs.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->gs.attrib = 0x0093; // read/write 

  // set up SS descr 
  vmcb->ss.selector = 0x0;
  vmcb->ss.base = 0x0;
  vmcb->ss.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->ss.attrib = 0x0093; // read/write 

  vmcb->idtr.limit = 0x03ff;

  // SVME needs to be set in EFER for vmrun to execute 
  vmcb->efer |= (1 << EFER_SVME);
   
  // set guest PAT to state at reset. 
  vmcb->g_pat = 0x0007040600070406ULL;

  // other-non general purpose registers/state 
  vmcb->guest_asid = 1; // ASID 0 reserved for host 
  vmcb->cpl = 0; // set cpl to 0 for real mode 

  // general purpose registers 
  vmcb->rax= 0x0ULL;
  vmcb->rsp= 0x0ULL;

  if(vcpu->isbsp){
    printf("\nBSP(0x%02x): copying boot-module to boot guest", vcpu->id);
  	memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)rpb->XtGuestOSBootModuleBase, rpb->XtGuestOSBootModuleSize);
    vmcb->rip = 0x7c00ULL;
  }else{

#ifdef __NESTED_PAGING__
      vmcb->cs.selector = (vcpu->sipivector * PAGE_SIZE_4K) >> 4;
      vmcb->cs.base = (vcpu->sipivector * PAGE_SIZE_4K);
      vmcb->rip = 0x0ULL;
#endif

  }
  vmcb->rflags = 0x0ULL;
  
  vmcb->cr0 = 0x00000010ULL;
  vmcb->cr2 = 0ULL;
  vmcb->cr3 = 0x0ULL;
  vmcb->cr4 = 0ULL;
  
  vmcb->dr6 = 0xffff0ff0ULL;
  vmcb->dr7 = 0x00000400ULL;
 
 
  // intercept all SVM instructions 
  vmcb->class2_intercepts_bitmask |= (u32)(SVM_CLASS2_INTERCEPT_VMRUN |
					  SVM_CLASS2_INTERCEPT_VMMCALL |
					  SVM_CLASS2_INTERCEPT_VMLOAD |
					  SVM_CLASS2_INTERCEPT_VMSAVE |
					  SVM_CLASS2_INTERCEPT_STGI |
					  SVM_CLASS2_INTERCEPT_CLGI |
					  SVM_CLASS2_INTERCEPT_SKINIT |
					  SVM_CLASS2_INTERCEPT_ICEBP);

	//INT 15h E820 hook enablement for VMX unrestricted guest mode
	//note: this only happens for the BSP
	if(vcpu->isbsp){
		printf("\nCPU(0x%02x, BSP): initializing INT 15 hook...", vcpu->id);
		_svm_int15_initializehook(vcpu);
	}


  //intercept NMIs, required for core quiescing support
  vmcb->class1_intercepts_bitmask |= (u32) SVM_CLASS1_INTERCEPT_NMI;

  //setup IO interception
  //memset((void *)g_svm_iopm, 0, SIZEOF_IOPM_BITMAP);   //clear bitmap buffer
  vmcb->iopm_base_pa = hva2spa((void *)vcpu->svm_vaddr_iobitmap);   //setup vmcb iopm
  vmcb->class1_intercepts_bitmask |= (u32) SVM_CLASS1_INTERCEPT_IOIO_PROT;

  //setup MSR interception
  memset((void *)g_svm_msrpm, 0, SIZEOF_MSRPM_BITMAP);   //clear bitmap buffer
  vmcb->msrpm_base_pa = hva2spa(g_svm_msrpm);   //setup vmcb msrpm
  vmcb->class1_intercepts_bitmask |= (u32) SVM_CLASS1_INTERCEPT_MSR_PROT;


  return;
}



//initialize partition monitor for a given CPU
void emhf_partition_arch_x86svm_initializemonitor(VCPU *vcpu){
  //initialize SVM
  _svm_initSVM(vcpu);

}

//setup guest OS state for the partition
void emhf_partition_arch_x86svm_setupguestOSstate(VCPU *vcpu){
	//setup VMCB
	_svm_initVMCB(vcpu);
	
}

//start executing the partition and guest OS
void emhf_partition_arch_x86svm_start(VCPU *vcpu){
    struct _svm_vmcbfields *vmcb;
    vmcb = (struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr;
    printf("\nCPU(0x%02x): Starting HVM using CS:EIP=0x%04x:0x%08x...", vcpu->id,
			(u16)vmcb->cs.selector, (u32)vmcb->rip);
    __svm_start_hvm(vcpu, hva2spa((void*)vcpu->vmcb_vaddr_ptr));
	//we never get here, if we do, we just return and our caller is responsible
	//for halting the core as something really bad happened!
}
	
//set legacy I/O protection for the partition
void emhf_partition_arch_x86svm_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype){
	u8 *bit_vector = (u8 *)vcpu->svm_vaddr_iobitmap;
	u32 byte_offset, bit_offset;
	u32 i;

	for(i=0; i < size; i++){
		byte_offset = (port+i) / 8;
		bit_offset = (port+i) % 8;
		if(prottype & PART_LEGACYIO_NOACCESS){
			bit_vector[byte_offset] |= (1 << bit_offset);	
		}else{
			prottype = PART_LEGACYIO_READWRITE;
			bit_vector[byte_offset] &= ~((1 << bit_offset));	
		}
	}
}
