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

// XMHF core initialization boostrap (init-bs) entry module
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xc-initbs.h>

#include <xc-init.h>

void xmhf_runtime_entry(void){

	//setup debugging	
	//xmhf_debug_init((char *)&xcbootinfo->debugcontrol_buffer);
	//_XDPRINTF_("\nxmhf-core: starting...");

   
  	//initialize basic platform elements
	//xmhf_baseplatform_initialize();

	//setup XMHF exception handler component
	//xmhf_xcphandler_initialize();

	#if defined (__DMAP__)
	xmhf_dmaprot_reinitialize();
	#endif

	//initialize richguest
	//xmhf_richguest_initialize();


	_XDPRINTF_("proceeding to initialize exception handling...\n");
	//setup platform exception handling
	xcinitbs_arch_initialize_exception_handling();
	_XDPRINTF_("exception handling initialized.\n");


	//_XDPRINTF_("\nXMHF Tester Finished!\n\n");
	//HALT();

	//initialize base platform with SMP 
	xmhf_baseplatform_smpinitialize();

	_XDPRINTF_("\nRuntime: We should NEVER get here!");
	HALT_ON_ERRORCOND(0);
}

///////
XMHF_SLAB("initbs")

XMHF_SLAB_DEFINTERFACE(
	XMHF_SLAB_DEFEXPORTFN(xmhf_runtime_entry, XMHF_SLAB_INITBS_FNXMHFRUNTIMEENTRY, XMHF_SLAB_FN_RETTYPE_NORMAL)
)

//XMHF_SLAB_DEFINTERFACEBARE(
//	xmhf_runtime_entry
//)
