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
 * EMHF partition component interface (x86 SVM backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <emhf.h>

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
  hsave_pa = __hva2spa__((void*)vcpu->hsave_vaddr_ptr);
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


//initialize partition monitor for a given CPU
void emhf_partition_arch_x86svm_initializemonitor(VCPU *vcpu){
  //initialize SVM
  _svm_initSVM(vcpu);

}
