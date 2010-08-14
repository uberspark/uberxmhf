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

/* entry.S - Entry and exit code for guest entry/exit 
 * Written for TrustVisor by Mark Luk and Arvind Seshadri
 * Cleaned up by Arvind Seshadri 
 */ 
#include <types.h>
#include <multiboot.h>
#include <paging.h>
#include <visor.h>
#include <processor.h>
#include <msr.h>
#include <visor.h>
	
/* the order to save registers is important because we 
 * reply on it to interpret some instruction during
 * interception. 
 * more details reference visor/intercepts-xxx.c 
 */
#define SV_SAVE_ALL_GREGS \
        pushl	%edi	; \
        pushl	%esi	; \
	pushl	%ebp	; \
	pushl	%esp    ; \
        pushl	%ebx	; \
        pushl	%edx	; \
        pushl	%ecx	; \
        pushl	%eax	; 
	
#define SV_RESTORE_ALL_GREGS \
	popl	%eax	; \
        popl	%ecx	; \
        popl	%edx	; \
        popl	%ebx	; \
	popl	%esp	; \
        popl	%ebp	; \
        popl	%esi	; \
        popl	%edi	; 

#define RESTORE_HOST_DEBUG_STATE \
	mov 	host_dr0, %eax	; \
	mov	%eax, %dr0	; \
	mov	host_dr1, %eax	; \
	mov	%eax, %dr1	; \
	mov	host_dr2, %eax	; \
	mov	%eax, %dr2	; \
	mov	host_dr3, %eax	; \
	mov	%eax, %dr3	; \
	mov	host_dr6, %eax	; \
	mov	%eax, %dr6	; \
	mov	host_dr7, %eax	; \
	mov	%eax, %dr7	; 

#define RESTORE_GUEST_DEBUG_STATE \
	xor	%ebx, %ebx	; \
	xor	%ecx, %ecx	; \
	xor	%edx, %edx	; \
	xor	%esi, %esi	; \
	mov	%dr0, %eax	; \
	mov	%eax, host_dr0	; \
	mov	%ebx, %dr0	; \
	mov	%dr1, %eax	; \
	mov	%eax, host_dr1	; \
	mov	%ecx, %dr1	; \
	mov	%dr2, %eax	; \
	mov	%eax, host_dr2	; \
	mov	%edx, %dr2	; \
	mov	%dr3, %eax	; \
	mov	%eax, host_dr3	; \
	mov	%esi, %dr3	;

/* no need to restore dr6 and dr7. these are restored by vmrun */
	
	.section ".text"
/* entry point for the runtime */
ENTRY(start_runtime)
	jmp	vmrun_label
/* entry point for vmexits from guest */
ENTRY(entry_point)
/* First save all guest gprs, including esp and eax which are already saved 
 * in the vmcb by vmexit. vmexit also restores TrustVisor's esp. So we 
 * TrustVisor's stack for saving. NOTE: We do not save the MMX or XMM 
 * regs since these are not used by TrustVisor.
 */

	SV_SAVE_ALL_GREGS
	stgi
/* Now pass the regs on stack as arguments to the handle_intercept function.
 * The agrument (in eax) is pointer to the struct of guest regs
 */
	mov	%esp, %eax
	call	handle_intercept	 

/* Intecept handled, return to guest using vmrun */
/* We do not save TrustVisor's gprs here since they do not contain
 * anything that needs to saved across a vmrun
   XXX SHOULDN'T WE ZERO THEM SO AS NOT TO LEAK SENSITIVE INFO? -Jon 2009.10.29
 */
	clgi
	SV_RESTORE_ALL_GREGS
ENTRY(vmrun_label)
	mov	relocated_visor_vmcb, %eax
	vmrun
/* #vmexit should drop us here */
	jmp	entry_point	
