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

// EMHF DMA protection component declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_DMAPROT_H__
#define __EMHF_DMAPROT_H__


#ifndef __ASSEMBLY__


//----------------------------------------------------------------------
//exported DATA 
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------

//return size (in bytes) of the memory buffer required for
//DMA protection for a given physical memory limit
u32 emhf_dmaprot_getbuffersize(u64 physical_memory_limit);


//"early" DMA protection initialization to setup minimal
//structures to protect a range of physical memory
//return 1 on success 0 on failure
u32 emhf_dmaprot_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);

//"normal" DMA protection initialization to setup required
//structures for DMA protection
//return 1 on success 0 on failure
u32 emhf_dmaprot_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);

//DMA protect a given region of memory, start_paddr is
//assumed to be page aligned physical memory address
void emhf_dmaprot_protect(u32 start_paddr, u32 size);

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------
u32 emhf_dmaprot_arch_getbuffersize(u64 physical_memory_limit);
u32 emhf_dmaprot_arch_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);
u32 emhf_dmaprot_arch_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);
void emhf_dmaprot_arch_protect(u32 start_paddr, u32 size);


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
u32 emhf_dmaprot_arch_x86svm_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);
u32 emhf_dmaprot_arch_x86svm_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);
void emhf_dmaprot_arch_x86svm_protect(u32 start_paddr, u32 size);


//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
u32 emhf_dmaprot_arch_x86vmx_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);
u32 emhf_dmaprot_arch_x86vmx_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);
void emhf_dmaprot_arch_x86vmx_protect(u32 start_paddr, u32 size);

//VMX VT-d page table buffers; we support a 3 level page-table walk, 
//4kb pdpt, 4kb pdt and 4kb pt and each entry in pdpt, pdt and pt is 64-bits
extern u8 g_vmx_vtd_pdp_table[] __attribute__(( section(".palign_data") )); 
extern u8 g_vmx_vtd_pd_tables[] __attribute__(( section(".palign_data") ));
extern u8 g_vmx_vtd_p_tables[] __attribute__(( section(".palign_data") ));

//VMX VT-d Root Entry Table (RET)
//the RET is 4kb, each root entry (RE) is 128-bits
//this gives us 256 entries in the RET, each corresponding to a PCI bus num. (0-255)
extern u8 g_vmx_vtd_ret[] __attribute__(( section(".palign_data") )); 

//VMX VT-d Context Entry Table (CET)
//each RE points to a context entry table (CET) of 4kb, each context entry (CE)
//is 128-bits which gives us 256 entries in the CET, accounting for 32 devices
//with 8 functions each as per the PCI spec.
extern u8 g_vmx_vtd_cet[] __attribute__(( section(".palign_data") ));




#endif	//__ASSEMBLY__

#endif //__EMHF_DMAPROT_H__
