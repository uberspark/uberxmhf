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

// v86monitor.h - Intel VT V86 monitor for real-mode code execution
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __V86M_H__
#define __V86M_H__

#define V86M_CR0_INITIALVALUE 	(0x00000020)	//real-mode, no paging

#define V86M_SELECTOR_TASK 0x0008
#define V86M_SELECTOR_LDTR 0x0010
#define V86M_SELECTOR_CODE 0x0004
#define V86M_SELECTOR_DATA 0x000C
#define V86M_SELECTOR_VRAM 0x0014
#define V86M_SELECTOR_FLAT 0x001C



#ifndef __ASSEMBLY__

void v86monitor_initialize(void);
void v86monitor_initializeguest(VCPU *vcpu);



extern u32 v86monitor_guest_gdt_base;
extern u16 v86monitor_guest_gdt_limit;
extern u32 v86monitor_guest_idt_base;
extern u16 v86monitor_guest_idt_limit;
extern u32 v86monitor_guest_reg_cr0;
extern u32 v86monitor_guest_reg_eax;
extern u32 v86monitor_guest_reg_ebx;
extern u32 v86monitor_guest_reg_ecx;
extern u32 v86monitor_guest_reg_edx;
extern u32 v86monitor_guest_reg_esi;
extern u32 v86monitor_guest_reg_edi;
extern u32 v86monitor_guest_reg_ebp;
extern u32 v86monitor_guest_reg_esp;
extern u32 v86monitor_guest_reg_eip;
extern u32 v86monitor_guest_reg_cs;
extern u32 v86monitor_guest_reg_ss;
extern u32 v86monitor_guest_reg_eflags;
extern u32 v86monitor_guest_reg_cr4;
extern u32 v86monitor_guest_reg_cr3;


#endif //__ASSEMBLY__

#endif //__V86M_H__

