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

//hardware_paging.h 
//definitions for intel extended page tables
//author: amit vasudevan (amitvasudevan@acm.org)
#ifndef _HARDWARE_PAGING_H_
#define _HARDWARE_PAGING_H_

#define MTRR_TYPE_UC   0x0
#define MTRR_TYPE_WC   0x1
#define MTRR_TYPE_WT   0x4
#define MTRR_TYPE_WP   0x5
#define MTRR_TYPE_WB   0x6
#define MTRR_TYPE_RESV  0x7
 

extern u8 vmx_ept_pml4_table[];
extern u8 vmx_ept_pdp_table[];
extern u8 vmx_ept_pd_tables[];
extern u8 vmx_ept_p_tables[];

void vmx_setupEPT(VCPU *vcpu);
void vmx_gathermemorytypes(VCPU *vcpu);
u32 vmx_getmemorytypeforphysicalpage(u64 pagebaseaddr);

#endif // __HARDWARE_PAGING_H_
