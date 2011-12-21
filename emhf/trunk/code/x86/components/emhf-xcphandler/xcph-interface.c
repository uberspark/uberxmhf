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


//initialize EMHF core exception handlers
void emhf_xcphandler_initialize(void){
	u32 *pexceptionstubs;
	u32 i;

	printf("\n%s: setting up runtime IDT...", __FUNCTION__);
	
	pexceptionstubs=(u32 *)&emhf_xcphandler_exceptionstubs;
	
	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		idtentry_t *idtentry=(idtentry_t *)((u32)&emhf_xcphandler_idt+ (i*8));
		idtentry->isrLow= (u16)pexceptionstubs[i];
		idtentry->isrHigh= (u16) ( (u32)pexceptionstubs[i] >> 16 );
		idtentry->isrSelector = __CS;
		idtentry->count=0x0;
		idtentry->type=0x8E;
	}
	
	printf("\n%s: IDT setup done.", __FUNCTION__);
}


//reset IDT to zeros
void emhf_xcphandler_resetIDT(void){
	memset((void *)emhf_xcphandler_idt_start, 0, EMHF_XCPHANDLER_IDTSIZE);	
	return;
}

//get IDT start address
u8 * emhf_xcphandler_get_idt_start(void){
	return (u8 *)&emhf_xcphandler_idt_start;
}


//EMHF exception handler routine
void emhf_xcphandler_hub(u32 vector, struct regs *r){
	u32 cpu_vendor = get_cpu_vendor_or_die();	//determine CPU vendor
	VCPU *vcpu;
	
	printf("\n%s: exception 0x%02x - handing off...", __FUNCTION__, vector);
	
	if(cpu_vendor == CPU_VENDOR_AMD){
		vcpu=_svm_getvcpu();
	}else{	//CPU_VENDOR_INTEL
	    vcpu=_vmx_getvcpu();
	}	
	
	printf("\nCPU(0x%02x): XtRtmExceptionHandler: Exception=0x%08X", vcpu->id, vector);
	printf("\nCPU(0x%02x): ESP=0x%08x", vcpu->id, r->esp);
	if(vector == 0x2){
		emhf_smpguest_eventhandler_nmiexception(vcpu, r);
		return;
	}	
}
