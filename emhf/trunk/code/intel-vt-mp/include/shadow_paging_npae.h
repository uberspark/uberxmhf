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

//shadow_paging.h 
//definitions for shadow paging (non-PAE)
//author: amit vasudevan (amitvasudevan@acm.org)
#ifndef _SHADOW_PAGING_NPAE_H_
#define _SHADOW_PAGING_NPAE_H_

//extern u32 __shadow_pdp_table[];
//extern u32 __shadow_pd_tables[];
//extern u32 __shadow_p_tables[];

extern u32 __shadow_npae_pd_table[];
extern u32 __shadow_npae_p_tables[];

extern u32 shadow_guest_CR3;

u32 shadow_page_fault(u32 cr2, u32 error_code);
void shadow_invalidate_page(u32 address);
u32 shadow_new_context(u32 guest_CR3);
//void shadow_copy(u32 gCR3);
u32 shadow_checkcontext(u32 root);

//guest physical address to host physical address, we have it
//unity mapped for our hypervisor. ie, gpa = hpa
#define gpa_to_hpa(x)	x

#define PFERR_PRESENT_MASK (1U << 0)
#define PFERR_WR_MASK (1U << 1)
#define PFERR_US_MASK (1U << 2)
#define PFERR_RSVD_MASK (1U << 3)
#define PFERR_ID_MASK (1U << 4)

//masks for AVL bits that we use
#define _PAGE_SHADOW_DIRTYWAITING		0x200	
#define _PAGE_SHADOW_ORIGINALRWBIT	0x400
#define _PAGE_SHADOW_UNUSEDAVL			0x800


#endif // __SHADOW_PAGING_NPAE_H_
