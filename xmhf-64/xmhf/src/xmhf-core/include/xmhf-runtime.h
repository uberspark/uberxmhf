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

// EMHF runtime component declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_RUNTIME_H__
#define __EMHF_RUNTIME_H__

#define DMAPROT_PHY_ADDR_SPACE_SIZE		(PA_PAGE_ALIGN_UP_1G(MAX_PHYS_ADDR))
#define DMAPROT_VMX_P4L_NPDT			(DMAPROT_PHY_ADDR_SPACE_SIZE >> PAGE_SHIFT_1G)

// 4-level PML4 page tables + 4KB root entry table + 4K context entry table per PCI bus
#define SIZE_G_RNTM_DMAPROT_BUFFER	(PAGE_SIZE_4K + PAGE_SIZE_4K + (PAGE_SIZE_4K * DMAPROT_VMX_P4L_NPDT) \
					+ (PAGE_SIZE_4K * DMAPROT_VMX_P4L_NPDT * PAE_PTRS_PER_PDT) \
					+ (PAGE_SIZE_4K)  						/* size of the root table = 4KB */						\
					+ (PAGE_SIZE_4K * PCI_BUS_MAX))			/* sizes of all context tables = 4KB * PCI_BUS_MAX */

#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//exported DATA
//----------------------------------------------------------------------

//runtime parameter block data area
//extern u8 arch_rpb[];
extern RPB arch_rpb;

//runtime parameter block pointer
extern RPB *rpb __attribute__(( section(".data") ));

//runtime DMA protection buffer
extern u8 g_rntm_dmaprot_buffer[] __attribute__((aligned(PAGE_SIZE_4K)));

//variable that is incremented by 1 by all cores that cycle through appmain
//successfully, this should be finally equal to g_midtable_numentries at
//runtime which signifies that EMHF appmain executed successfully on all
//cores
extern volatile u32 g_appmain_success_counter __attribute__(( section(".data") ));

//SMP lock for the above variable
extern volatile u32 g_lock_appmain_success_counter __attribute__(( section(".data") ));

//----------------------------------------------------------------------
//exported FUNCTIONS
//----------------------------------------------------------------------

//entry point of EMHF runtime; this is where we get control from the SL
void xmhf_runtime_entry(void);

//EMHF runtime main function; gets control in the context of each core
void xmhf_runtime_main(VCPU *vcpu, u32 isEarlyInit);

void xmhf_runtime_shutdown(VCPU *vcpu, struct regs *r);

//DMAP related functions
#if defined(__DRT__) || defined(__DMAP__)
void vmx_dmar_zap(spa_t dmaraddrphys);
spa_t vmx_find_dmar_paddr(VTD_DMAR *dmar);
#endif /* defined(__DRT__) || defined(__DMAP__) */
#if defined(__DRT__) && !defined(__DMAP__)
void vmx_eap_zap(void);
#endif /* defined(__DRT__) && !defined(__DMAP__) */

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------



//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//x86svm SUBARCH. INTERFACES
//----------------------------------------------------------------------


#endif //__ASSEMBLY__

#endif //__EMHF_RUNTIME_H__
