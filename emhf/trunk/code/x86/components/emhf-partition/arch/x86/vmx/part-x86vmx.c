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

/*
 * EMHF partition component interface (x86 VMX backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <emhf.h>

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


//initialize partition monitor for a given CPU
void emhf_partition_arch_x86vmx_initializemonitor(VCPU *vcpu){

  //initialize VT
  _vmx_initVT(vcpu);

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

