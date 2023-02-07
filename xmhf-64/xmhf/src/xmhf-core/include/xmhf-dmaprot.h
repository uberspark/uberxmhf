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

/// @brief The invalid handler of the IOMMU PageTable
#define IOMMU_PT_INVALID	0xFFFFFFFF

/// @brief The IOMMU PT ID of the untrusted OS
#define UNTRUSTED_OS_IOMMU_PT_ID	1

/// @brief The handler type of the IOMMU PageTable
typedef uint32_t iommu_pt_t;

/// @brief The descriptor to locate a Device
// [TODO] We only support PCI/PCIe devices at current.
typedef union
{
	struct {
		unsigned short	func:3,
			dev:5,
			bus:8;
		char __resvs[sizeof(unsigned long) - sizeof(unsigned short)];
	} __attribute__ ((packed));
	unsigned long 	raw;
} DEVICEDESC;

//----------------------------------------------------------------------
//exported DATA
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS
//----------------------------------------------------------------------

typedef enum
{
    /// @brief Invalid type of IOMMU PT.
    IOMMU_PT_TYPE_INVALID = 0,

    /// @brief Support DMA accesses to secure domain's memory only.
    /// [NOTE] This type of IOMMU PT allows DMA destinations to be paddrs of the secure domain.
    IOMMU_PT_TYPE_S_EXCLUSIVE = 1,

    /// @brief Support DMA accesses to both secure domain's memory and non-secure domain's memory.
    /// [NOTE] This type of IOMMU PT requires that DMA destinations must be spaddrs instead of paddrs of
    /// secure/non-secure domains.
    IOMMU_PT_TYPE_S_NS_SHARED = 2
} IOMMU_PT_TYPE;

/// @brief Initialize the IOMMU (DMA Protection to the main memory) subsystem
extern void xmhf_iommu_init(void);

/// @brief Finalize the IOMMU subsystem
extern void xmhf_iommu_fini(void);

extern uint32_t iommu_is_pt_s_exclusive(iommu_pt_t pt_handle, bool* out_result);
extern uint32_t iommu_is_pt_s_ns_shared(iommu_pt_t pt_handle, bool* out_result);

/// @brief Create a new IOMMU Page Table
extern iommu_pt_t xmhf_iommu_pt_create(IOMMU_PT_TYPE type);

/// @brief Destroy an IOMMU Page Table
extern bool xmhf_iommu_pt_destroy(iommu_pt_t pt_handle);

// Mapping flags
#define DMA_ALLOW_ACCESS	1
#define DMA_DENY_ACCESS		2

/// @brief Map <spa> with <gpa> in the IOMMU PT
extern bool xmhf_iommu_pt_map(iommu_pt_t pt_handle, gpa_t gpa, spa_t spa, uint32_t flags);

/// @brief Load the IOMMU PT for a specific device
extern bool xmhf_iommu_bind_device(iommu_pt_t pt_handle, DEVICEDESC* device);

/// @brief Bind the untrusted OS's default IOMMU PT to the specific device
extern bool xmhf_iommu_unbind_device(DEVICEDESC* device);

/// @brief Map <spa> with <gpa> in all IOMMU_PT_TYPE_S_NS_SHARED IOMMU PTs.
/// [NOTE] This function is needed when moving memory between S and NS domains. Otherwise, a shared IOMMU PT created
/// by a SecProcess ealier may map isolated memory given to other SecProcesses later. This violates memory separation
/// between SecProcesses.
/// [TODO][Issue 60] SecBase needs to prove: All IOMMU_PT_TYPE_S_NS_SHARED IOMMU PTs map NS domain's memory and given
/// S domain's memory, but not any other S domain's memory.
extern bool xmhf_iommu_all_shared_pts_map(gpa_t gpa, uint32_t flags);

//return size (in bytes) of the memory buffer required for
//DMA protection for a given physical memory limit
u32 xmhf_dmaprot_getbuffersize(u64 physical_memory_limit);


//"early" DMA protection initialization to setup minimal
//structures to protect a range of physical memory
//return 1 on success 0 on failure
u32 xmhf_dmaprot_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);

//"normal" DMA protection initialization to setup required
//structures for DMA protection
//return 1 on success 0 on failure
u32 xmhf_dmaprot_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);

// Call memprot to protect DRHD pages. Should be called by each CPU after
// xmhf_dmaprot_initialize().
void xmhf_dmaprot_protect_drhd(VCPU *vcpu);

// Enable the DMA protection HW
// [NOTE] This function must be separated from <xmhf_dmaprot_initialize>. Otherwise, misconfigured devices can have a 
// chance to modify XMHF binary between the function <xmhf_dmaprot_initialize> and <xmhf_dmaprot_protect> inside 
// <xmhf_runtime_entry>
//return 1 on success 0 on failure
u32 xmhf_dmaprot_enable(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);

//DMA protect a given region of memory, start_paddr is
//assumed to be page aligned physical memory address
void xmhf_dmaprot_protect(spa_t start_paddr, size_t size);

extern void xmhf_dmaprot_unprotect(spa_t start_paddr, size_t size);

extern void xmhf_dmaprot_invalidate_cache(void);

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------
u32 xmhf_dmaprot_arch_getbuffersize(u64 physical_memory_limit);
u32 xmhf_dmaprot_arch_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);
u32 xmhf_dmaprot_arch_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);
void xmhf_dmaprot_arch_protect_drhd(VCPU *vcpu);
u32 xmhf_dmaprot_arch_enable(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);
void xmhf_dmaprot_arch_protect(spa_t start_paddr, size_t size);

extern void xmhf_dmaprot_arch_unprotect(spa_t start_paddr, size_t size);

extern void xmhf_dmaprot_arch_invalidate_cache(void);


//----------------------------------------------------------------------
//x86_vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
// Capabilities of Intel VT-d HW
struct dmap_vmx_cap
{
	u32 nd:3;
	u32 sagaw:5;
	u32 _reserved1:24;
} __attribute__ ((packed));

//----------------------------------------------------------------------
//vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
u32 xmhf_dmaprot_arch_x86_vmx_earlyinitialize(sla_t protectedbuffer_paddr,
	sla_t protectedbuffer_vaddr, size_t protectedbuffer_size,
	sla_t memregionbase_paddr, u32 memregion_size);
u32 xmhf_dmaprot_arch_x86_vmx_initialize(spa_t protectedbuffer_paddr,
	hva_t protectedbuffer_vaddr, size_t protectedbuffer_size);
void xmhf_dmaprot_arch_x86_vmx_protect_drhd(VCPU *vcpu);
u32 xmhf_dmaprot_arch_x86_vmx_enable(spa_t protectedbuffer_paddr,
	hva_t protectedbuffer_vaddr, size_t protectedbuffer_size);
void xmhf_dmaprot_arch_x86_vmx_protect(spa_t start_paddr, size_t size);
extern void xmhf_dmaprot_arch_x86_vmx_unprotect(spa_t start_paddr, size_t size);
extern void xmhf_dmaprot_arch_x86_vmx_invalidate_cache(void);



/********* Support hypapps to control igfx's IOMMU *********/
#ifdef __XMHF_ALLOW_HYPAPP_DISABLE_IGFX_IOMMU__
//! \brief Enable the IOMMU servicing the integrated GPU only. Other IOMMUs are not modified.
//!
//! @return Return true on success
extern bool xmhf_dmaprot_arch_x86_vmx_enable_igfx_iommu(void);

//! \brief Disable the IOMMU servicing the integrated GPU only. Other IOMMUs are not modified.
//!
//! @return Return true on success
extern bool xmhf_dmaprot_arch_x86_vmx_disable_igfx_iommu(void);
#endif // __XMHF_ALLOW_HYPAPP_DISABLE_IGFX_IOMMU__




/********* Debug functions *********/
extern void xmhf_dmaprot_arch_x86_vmx_print_and_clear_fault_registers(void);
extern void xmhf_dmaprot_arch_x86_vmx_restart_dma_iommu(void);
extern void xmhf_dmaprot_arch_x86_vmx_disable_dma_iommu(void);
extern void xmhf_dmaprot_arch_x86_vmx_print_tes(char* s);


//----------------------------------------------------------------------
//svm SUBARCH. INTERFACES
//----------------------------------------------------------------------
u32 xmhf_dmaprot_arch_x86_svm_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);
u32 xmhf_dmaprot_arch_x86_svm_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);
void xmhf_dmaprot_arch_x86_svm_protect(u32 start_paddr, u32 size);
extern void xmhf_dmaprot_arch_x86_svm_invalidate_cache(void);

//VMX VT-d page table buffers; we support a 3 level page-table walk,
//4kb pdpt, 4kb pdt and 4kb pt and each entry in pdpt, pdt and pt is 64-bits
//extern u8 g_vmx_vtd_pdp_table[] __attribute__((aligned(PAGE_SIZE_4K)));
//extern u8 g_vmx_vtd_pd_tables[] __attribute__((aligned(PAGE_SIZE_4K)));
//extern u8 g_vmx_vtd_p_tables[] __attribute__((aligned(PAGE_SIZE_4K)));

//VMX VT-d Root Entry Table (RET)
//the RET is 4kb, each root entry (RE) is 128-bits
//this gives us 256 entries in the RET, each corresponding to a PCI bus num. (0-255)
extern u8 g_vmx_vtd_ret[] __attribute__((aligned(PAGE_SIZE_4K)));

//VMX VT-d Context Entry Table (CET)
//each RE points to a context entry table (CET) of 4kb, each context entry (CE)
//is 128-bits which gives us 256 entries in the CET, accounting for 32 devices
//with 8 functions each as per the PCI spec.
extern u8 g_vmx_vtd_cet[] __attribute__((aligned(PAGE_SIZE_4K)));


#endif	//__ASSEMBLY__

#endif //__EMHF_DMAPROT_H__
