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

// appmain.c
// emhf application main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h>

#define	QUIESCE_HYPERCALL		0x44550002

// application main
u32 emhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb){
  (void)apb;	//unused
  printf("\nCPU(0x%02x): Hello world from Quiesce EMHF hyperapp!", vcpu->id);
  return APP_INIT_SUCCESS;  //successful
}

//returns APP_SUCCESS if we handled the hypercall else APP_ERROR
u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r){
	u32 status=APP_SUCCESS;
	u32 hypercall_number = r->ebx;

	switch(hypercall_number){
		case QUIESCE_HYPERCALL:
			printf("\nCPU(0x%02x): quiesce test hypercall received...", vcpu->id);
			break;
			
		default:
			printf("\nCPU(0x%02x): unhandled hypercall (0x%08x)!", vcpu->id, r->ebx);
			break;
	}
	
	return status;
}

//handles EMHF shutdown callback
//note: should not return
void emhf_app_handleshutdown(VCPU *vcpu, struct regs *r){
	(void)r; //unused
	emhf_baseplatform_reboot(vcpu);				
}

//handles h/w pagetable violations
//for now this always returns APP_SUCCESS
u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
      struct regs *r,
      u64 gpa, u64 gva, u64 violationcode){
	u32 status = APP_SUCCESS;

	(void)vcpu; //unused
	(void)r; //unused
	(void)gpa; //unused
	(void)gva; //unused
	(void)violationcode; //unused

	return status;
}


//handles i/o port intercepts
//returns either APP_IOINTERCEPT_SKIP or APP_IOINTERCEPT_CHAIN
u32 emhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, 
  u32 portnum, u32 access_type, u32 access_size){
	(void)vcpu; //unused
	(void)r; //unused
	(void)portnum; //unused
	(void)access_type; //unused
	(void)access_size; //unused

 	return APP_IOINTERCEPT_CHAIN;
}
