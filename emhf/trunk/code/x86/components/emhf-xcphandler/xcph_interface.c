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

/* 
 * EMHF exception handler component interface
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
#include <emhf.h>

//rpb->XtVmmIdtFunctionPointers
//rpb->XtVmmIdtEntries
//rpb->XtVmmIdt

//initialize EMHF core exception handlers
void emhf_xcphandler_initialize(void){
		 	//setup runtime IDT
		{
			u32 *fptr, idtbase_virt, idtbase_rel;
			u32 i;

			printf("\nSL: setting up runtime IDT...");
			fptr=hva2sla(rpb->XtVmmIdtFunctionPointers);
			idtbase_virt= *(u32 *)(hva2sla(rpb->XtVmmIdt + 2));
			idtbase_rel= (uintptr_t)(hva2sla(idtbase_virt));
			printf("\n	fptr at virt=%08x, rel=%08x", (u32)rpb->XtVmmIdtFunctionPointers,
					(u32)fptr);
			printf("\n	idtbase at virt=%08x, rel=%08x", (u32)idtbase_virt,
					(u32)idtbase_rel);

			for(i=0; i < rpb->XtVmmIdtEntries; i++){
				idtentry_t *idtentry=(idtentry_t *)((u32)idtbase_rel+ (i*8));
				//printf("\n	%u: idtentry=%08x, fptr=%08x", i, (u32)idtentry, fptr[i]);
				idtentry->isrLow= (u16)fptr[i];
				idtentry->isrHigh= (u16) ( (u32)fptr[i] >> 16 );
				idtentry->isrSelector = __CS;
				idtentry->count=0x0;
				idtentry->type=0x8E;
			}
			printf("\nSL: setup runtime IDT.");
		}

	
	
}


//reset IDT to zeros
void emhf_xcphandler_resetIDT(void){
	memset((void *)emhf_xcphandler_idt_start, 0, EMHF_XCPHANDLER_IDTSIZE);	
	return;
}
