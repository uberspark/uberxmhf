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

// EMHF exception handler component
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_XCPHANDLER_H__
#define __EMHF_XCPHANDLER_H__

#define	EMHF_XCPHANDLER_MAXEXCEPTIONS	32
#define EMHF_XCPHANDLER_IDTSIZE			(EMHF_XCPHANDLER_MAXEXCEPTIONS * 8)

#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//exported DATA

//array of exception handler stubs
extern u8 xmhf_xcphandler_exceptionstubs[];

//IDT descriptor
extern u8 xmhf_xcphandler_idt[];

//start of interrupt descriptor table
extern u8 xmhf_xcphandler_idt_start[];

//----------------------------------------------------------------------
//exported FUNCTIONS

//initialize EMHF core exception handlers
void xmhf_xcphandler_initialize(void);

//get IDT start address
u8 * xmhf_xcphandler_get_idt_start(void);

//EMHF exception handler hub
void xmhf_xcphandler_hub(uintptr_t vector, struct regs *r);


//----------------------------------------------------------------------
// generic arch. interfaces

//obtain the vcpu of the currently executing core
VCPU *_svm_and_vmx_getvcpu(void);

//initialize EMHF core exception handlers
void xmhf_xcphandler_arch_initialize(void);

//get IDT start address
u8 * xmhf_xcphandler_arch_get_idt_start(void);

//EMHF exception handler hub
void xmhf_xcphandler_arch_hub(uintptr_t vector, struct regs *r);




#endif	//__ASSEMBLY__

#endif //__EMHF_XCPHANDLER_H__
