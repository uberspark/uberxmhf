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

// EMHF DMA protection component declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_DMAPROT_H__
#define __EMHF_DMAPROT_H__


#ifndef __ASSEMBLY__

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


//x86 SVM backend
u32 emhf_dmaprot_arch_x86svm_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);
u32 emhf_dmaprot_arch_x86svm_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);
void emhf_dmaprot_arch_x86svm_protect(u32 start_paddr, u32 size);


//x86 VMX backend
u32 emhf_dmaprot_arch_x86vmx_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size);
u32 emhf_dmaprot_arch_x86vmx_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size);
void emhf_dmaprot_arch_x86vmx_protect(u32 start_paddr, u32 size);


#endif	//__ASSEMBLY__

#endif //__EMHF_DMAPROT_H__
