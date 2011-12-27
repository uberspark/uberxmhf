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
extern u32 emhf_xcphandler_exceptionstubs[]; 

//IDT descriptor
extern u8 emhf_xcphandler_idt[];

//start of interrupt descriptor table 
extern u8 emhf_xcphandler_idt_start[];

//----------------------------------------------------------------------
//exported FUNCTIONS 

//initialize EMHF core exception handlers
void emhf_xcphandler_initialize(void);

//reset IDT to zeros
void emhf_xcphandler_resetIDT(void);

//get IDT start address
u8 * emhf_xcphandler_get_idt_start(void);

//EMHF exception handler hub
void emhf_xcphandler_hub(u32 vector, struct regs *r);


//----------------------------------------------------------------------
// generic arch. interfaces

//initialize EMHF core exception handlers
void emhf_xcphandler_arch_initialize(void);

//reset IDT to zeros
void emhf_xcphandler_arch_resetIDT(void);

//get IDT start address
u8 * emhf_xcphandler_arch_get_idt_start(void);

//EMHF exception handler hub
void emhf_xcphandler_arch_hub(u32 vector, struct regs *r);




#endif	//__ASSEMBLY__

#endif //__EMHF_XCPHANDLER_H__
