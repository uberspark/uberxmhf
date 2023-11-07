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
 * EMHF base platform component interface, x86 svm backend
 * smp related functions
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//allocate and setup VCPU structure for all the CPUs
void xmhf_baseplatform_arch_x86svm_allocandsetupvcpus(u32 cpu_vendor){
  u32 i;
  u32 npt_current_asid=ASID_GUEST_KERNEL;
  VCPU *vcpu;

  printf("\n%s: g_cpustacks range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (hva_t)g_cpustacks, (hva_t)g_cpustacks + (RUNTIME_STACK_SIZE * MAX_VCPU_ENTRIES),
        RUNTIME_STACK_SIZE);
  printf("\n%s: g_vcpubuffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (hva_t)g_vcpubuffers, (hva_t)g_vcpubuffers + (SIZE_STRUCT_VCPU * MAX_VCPU_ENTRIES),
        SIZE_STRUCT_VCPU);
  printf("\n%s: g_svm_hsave_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (hva_t)g_svm_hsave_buffers, (hva_t)g_svm_hsave_buffers + (8192 * MAX_VCPU_ENTRIES),
        8192);
  printf("\n%s: g_svm_vmcb_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (hva_t)g_svm_vmcb_buffers, (hva_t)g_svm_vmcb_buffers + (8192 * MAX_VCPU_ENTRIES),
        8192);
  printf("\n%s: g_svm_npt_pdpt_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (hva_t)g_svm_npt_pdpt_buffers, (hva_t)g_svm_npt_pdpt_buffers + (4096 * MAX_VCPU_ENTRIES),
        4096);
  printf("\n%s: g_svm_npt_pdts_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (hva_t)g_svm_npt_pdts_buffers, (hva_t)g_svm_npt_pdts_buffers + (16384 * MAX_VCPU_ENTRIES),
        16384);
  printf("\n%s: g_svm_npt_pts_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (hva_t)g_svm_npt_pts_buffers, (hva_t)g_svm_npt_pts_buffers + ((2048*4096) * MAX_VCPU_ENTRIES),
        (2048*4096));

  for(i=0; i < g_midtable_numentries; i++){
    vcpu = (VCPU *)((hva_t)g_vcpubuffers + (hva_t)(i * SIZE_STRUCT_VCPU));
    #ifndef __XMHF_VERIFICATION__
    memset((void *)vcpu, 0, sizeof(VCPU));
    #endif

    vcpu->cpu_vendor = cpu_vendor;

#ifdef __AMD64__
    vcpu->rsp = ((hva_t)g_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;
#elif defined(__I386__)
    vcpu->esp = ((hva_t)g_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
    vcpu->hsave_vaddr_ptr = ((hva_t)g_svm_hsave_buffers + (i * 8192));
    vcpu->vmcb_vaddr_ptr = (struct _svm_vmcbfields *)((hva_t)g_svm_vmcb_buffers + (i * 8192));

	//allocate SVM IO bitmap region and clear it
	vcpu->svm_vaddr_iobitmap = (hva_t)g_svm_iobitmap_buffer;
	#ifndef __XMHF_VERIFICATION__
	memset( (void *)vcpu->svm_vaddr_iobitmap, 0, (3*PAGE_SIZE_4K));
	#endif

    {
      u32 npt_pdpt_base, npt_pdts_base, npt_pts_base;
      npt_pdpt_base = ((hva_t)g_svm_npt_pdpt_buffers + (i * 4096));
      npt_pdts_base = ((hva_t)g_svm_npt_pdts_buffers + (i * 16384));
      npt_pts_base = ((hva_t)g_svm_npt_pts_buffers + (i * (2048*4096)));
      vcpu->npt_vaddr_ptr = npt_pdpt_base;
      vcpu->npt_vaddr_pdts = npt_pdts_base;
      vcpu->npt_vaddr_pts = npt_pts_base;
      vcpu->npt_asid = npt_current_asid;
      npt_current_asid++;
    }

    vcpu->id = g_midtable[i].cpu_lapic_id;
    vcpu->idx = i;
    vcpu->sipivector = 0;
    vcpu->sipireceived = 0;

    g_midtable[i].vcpu_vaddr_ptr = (hva_t)vcpu;
#ifdef __AMD64__
    printf("\nCPU #%u: vcpu_vaddr_ptr=0x%08x, rsp=0x%16lx", i, g_midtable[i].vcpu_vaddr_ptr,
      vcpu->rsp);
#elif defined(__I386__)
    printf("\nCPU #%u: vcpu_vaddr_ptr=0x%08x, esp=0x%08x", i, g_midtable[i].vcpu_vaddr_ptr,
      vcpu->esp);
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
    printf("\n  hsave_vaddr_ptr=0x%08x, vmcb_vaddr_ptr=0x%08x", vcpu->hsave_vaddr_ptr,
          vcpu->vmcb_vaddr_ptr);
  }
}

//wake up application processors (cores) in the system
void xmhf_baseplatform_arch_x86svm_wakeupAPs(void){
	//step-1: setup AP boot-strap code at in the desired physical memory location
	//note that we need an address < 1MB since the APs are woken up in real-mode
	//we choose 0x10000 physical or 0x1000:0x0000 logical
  {
    _ap_cr3_value = read_cr3();
    _ap_cr4_value = read_cr4();
    #ifndef __XMHF_VERIFICATION__
    memcpy((void *)0x10000, (void *)_ap_bootstrap_start, (uintptr_t)_ap_bootstrap_end - (uintptr_t)_ap_bootstrap_start + 1);
    #endif
  }

	//step-2: wake up the APs sending the INIT-SIPI-SIPI sequence as per the
	//MP protocol. Use the APIC for IPI purposes.
  printf("\nBSP: Using APIC to awaken APs...");
  xmhf_baseplatform_arch_x86_wakeupAPs();
  printf("\nBSP: APs should be awake.");
}
