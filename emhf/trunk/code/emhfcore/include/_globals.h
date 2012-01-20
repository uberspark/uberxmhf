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

/**
 * globals.h - contains information about global variables used
 * throughout the hypervisor. Trying to keep them all in one place.
 */

#ifndef __GLOBALS_H__
#define __GLOBALS_H__

#ifndef __ASSEMBLY__






//defined in runtimesup.S(.text), this is the start of the real-mode AP
//bootstrap code
extern u32 _ap_bootstrap_start[];

//defined in runtimesup.S(.text), this is the end of the real-mode AP
//bootstrap code
extern u32 _ap_bootstrap_end[];

//defined in runtimesup.S(.text), this is the MLE Join stucture to
//bring up the APs
extern u32 _mle_join_start[];

//the CR3 value to be loaded by the AP boot-strap code is placed in this
//variable by the runtime before waking up the APs
//defined in runtimesup.S(.text)
extern u32 _ap_cr3_value;

//the CR4 value to be loaded by the AP boot-strap code is placed in this
//variable by the runtime before waking up the APs
//defined in runtimesup.S(.text)
extern u32 _ap_cr4_value;


#if defined (__TEST_CPU_QUIESCE__)
	//queisce test global variables
	//quiesce cpu counter and corresponding lock
	extern u32 g_quiesce_cpu_counter __attribute__(( section(".data") ));
	extern u32 g_lock_quiesce_cpu_counter __attribute__(( section(".data") ));
#endif



   
//variable that is used to de-link the INT 15 handler, if 1 then signifies that
//we have processed E820 requests and its safe to de-link
extern u32 g_svm_ine820handler __attribute__(( section(".data") ));





//SVM VM_HSAVE buffers 
extern u8 g_svm_hsave_buffers[]__attribute__(( section(".palign_data") ));

//SVM VMCB buffers 
extern u8 g_svm_vmcb_buffers[]__attribute__(( section(".palign_data") )); 

//SVM IO bitmap buffer
extern u8 g_svm_iopm[]__attribute__(( section(".palign_data") )); 

//SVM MSR bitmap buffer
extern u8 g_svm_msrpm[]__attribute__(( section(".palign_data") ));

//SVM DEV bitmap buffer
extern u8 g_svm_dev_bitmap[]__attribute__(( section(".palign_data") ));



//VMX VMCS read-only field encodings
extern struct _vmx_vmcsrofields_encodings g_vmx_vmcsrofields_encodings[] __attribute__(( section(".data") ));

//count of VMX VMCS read-only fields
extern unsigned int g_vmx_vmcsrofields_encodings_count __attribute__(( section(".data") ));

//VMX VMCS read-write field encodings
extern struct _vmx_vmcsrwfields_encodings g_vmx_vmcsrwfields_encodings[] __attribute__(( section(".data") ));

//count of VMX VMCS read-write fields
extern unsigned int g_vmx_vmcsrwfields_encodings_count __attribute__(( section(".data") ));

//VMX VMXON buffers
extern u8 g_vmx_vmxon_buffers[] __attribute__(( section(".palign_data") ));

//VMX VMCS buffers
extern u8 g_vmx_vmcs_buffers[] __attribute__(( section(".palign_data") ));
		
//VMX IO bitmap buffers
extern u8 g_vmx_iobitmap_buffers[] __attribute__(( section(".palign_data") ));
		
//VMX guest and host MSR save area buffers
extern u8 g_vmx_msr_area_host_buffers[] __attribute__(( section(".palign_data") ));
extern u8 g_vmx_msr_area_guest_buffers[] __attribute__(( section(".palign_data") ));

//VMX MSR bitmap buffers
extern u8 g_vmx_msrbitmap_buffers[] __attribute__(( section(".palign_data") ));





//external isolation layer backends
//extern struct isolation_layer g_isolation_layer_svm;
//extern struct isolation_layer g_isolation_layer_vmx;

//isolation layer abstraction
//extern struct isolation_layer *g_isl __attribute__(( section(".data") ));;

//external EMHF library interface backends
//extern struct emhf_library g_emhf_library_svm;
//extern struct emhf_library g_emhf_library_vmx;

//EMHF library interface abstraction
//extern struct emhf_library *g_libemhf __attribute__(( section(".data") )); 

//function that initializes the runtime global variables
//void runtime_globals_init(void);

#endif //__ASSEMBLY__


#endif /* __GLOBALS_H__ */
