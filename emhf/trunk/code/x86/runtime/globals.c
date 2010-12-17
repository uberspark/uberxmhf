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

//globals.c
//author: amit vasudevan (amitvasudevan@acm.org)
//global declarations and definitions for the runtime

#include <target.h>
#include <globals.h>

//__grub_e820list
//system e820 map
E820MAP g_e820map[MAX_E820_ENTRIES] __attribute__(( section(".data") ));

//	.global __mp_cpuinfo
//	__mp_cpuinfo:
//	.fill SIZE_STRUCT_PCPU * MAX_PCPU_ENTRIES, 1, 0

//SMP CPU map; lapic id, base, ver and bsp indication for each available core
PCPU	g_cpumap[MAX_PCPU_ENTRIES] __attribute__(( section(".data") ));

//runtime stacks for individual cores
//  .global __cpustacks
//  __cpustacks:
//  .fill RUNTIME_STACK_SIZE * MAX_PCPU_ENTRIES, 1, 0
u8 g_cpustacks[RUNTIME_STACK_SIZE * MAX_PCPU_ENTRIES] __attribute__(( section(".stack") ));


//  .section .data
//  .align 4
//  .global __vcpubuffers
//  __vcpubuffers:
//  .fill SIZE_STRUCT_VCPU * MAX_VCPU_ENTRIES, 1, 0
//VCPU structure for each "guest OS" core
VCPU g_vcpubuffers[MAX_VCPU_ENTRIES] __attribute__(( section(".data") ));

//------------------------------------------------------------------------------    
//.section  .data
//  .align 8
//  .global __midtable
//  __midtable:
//  .fill (SIZE_STRUCT_MIDTAB * MAX_MIDTAB_ENTRIES), 1, 0
//master id table, contains core lapic id to VCPU mapping information
MIDTAB g_midtable[MAX_MIDTAB_ENTRIES] __attribute__(( section(".data") ));


//number of entries in the master id table, in essence the number of 
//physical cores in the system
u32 g_midtable_numentries __attribute__(( section(".data") )) = 0;

//variable that is incremented by 1 by all cores that boot up, this should
//be finally equal to g_midtable_numentries at runtime which signifies
//that all physical cores have been booted up and initialized by the runtime
u32 g_cpus_active __attribute__(( section(".data") )) = 0;

//SMP lock for the above variable
u32 g_lock_cpus_active __attribute__(( section(".data") )) = 1;
    
//variable that is set to 1 by the BSP after rallying all the other cores.
//this is used by the application cores to enter the "wait-for-SIPI" state    
u32 g_ap_go_signal __attribute__(( section(".data") )) = 0;

//SMP lock for the above variable
u32 g_lock_ap_go_signal __attribute__(( section(".data") )) = 1;

//variable that is incremented by 1 by all cores that cycle through appmain
//successfully, this should be finally equal to g_midtable_numentries at
//runtime which signifies that EMHF appmain executed successfully on all
//cores
u32 g_appmain_success_counter __attribute__(( section(".data") )) = 0;

//SMP lock for the above variable
u32 g_lock_appmain_success_counter __attribute__(( section(".data") )) = 1;



//runtime parameter block pointer 
RPB *rpb __attribute__(( section(".data") )); 


//------------------------------------------------------------------------------
//isolation layer specific runtime globals
//these are global variables accessed across islayer.c, islayersup.S and
//apic.c



/**
 * Isolation Layer (islayer.c)
 */

//the quiesce counter, all CPUs except for the one requesting the
//quiesce will increment this when they get their quiesce signal
u32 g_svm_quiesce_counter __attribute__(( section(".data") )) = 0;

//SMP lock to access the above variable
u32 g_svm_lock_quiesce_counter __attribute__(( section(".data") )) = 1; 

//resume counter to rally all CPUs after resumption from quiesce
u32 g_svm_quiesce_resume_counter __attribute__(( section(".data") )) = 0;

//SMP lock to access the above variable
u32 g_svm_lock_quiesce_resume_counter __attribute__(( section(".data") )) = 1; 
    
//the "quiesce" variable, if 1, then we have a quiesce in process
u32 g_svm_quiesce __attribute__(( section(".data") )) = 0;;      

//SMP lock to access the above variable
u32 g_svm_lock_quiesce __attribute__(( section(".data") )) = 1; 
    
//resume signal, becomes 1 to signal resume after quiescing
u32 g_svm_quiesce_resume_signal __attribute__(( section(".data") )) = 0;  

//SMP lock to access the above variable
u32 g_svm_lock_quiesce_resume_signal __attribute__(( section(".data") )) = 1; 
    
//variable that is used to de-link the INT 15 handler, if 1 then signifies that
//we have processed E820 requests and its safe to de-link
u32 g_svm_ine820handler __attribute__(( section(".data") )) = 0;


//apic.c

//the BSP LAPIC base address
u32 g_svm_lapic_base __attribute__(( section(".data") )) = 0;




//4k buffer which is the virtual LAPIC page that guest reads and writes from/to
//during INIT-SIPI-SIPI emulation
	//virtual LAPIC page for BSP to track SIPI
	//.global virtual_LAPIC_base
	//virtual_LAPIC_base:
	// .fill 4096, 1, 0
u8 g_svm_virtual_LAPIC_base[PAGE_SIZE_4K] __attribute__(( section(".palign_data") ));


//  .global svm_npt_pdpt_buffers
//  svm_npt_pdpt_buffers:
//   .fill 4096 * MAX_VCPU_ENTRIES, 1, 0
//SVM NPT PDPT buffers
u8 g_svm_npt_pdpt_buffers[PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));
  
//  .global svm_npt_pdts_buffers
//  svm_npt_pdts_buffers:
//    .fill (4*4096)* MAX_VCPU_ENTRIES, 1, 0
//SVM NPT PDT buffers
u8 g_svm_npt_pdts_buffers[PAE_PTRS_PER_PDPT * PAGE_SIZE_4K * MAX_VCPU_ENTRIES]__attribute__(( section(".palign_data") ));

//	.global svm_npt_pts_buffers
//	svm_npt_pts_buffers:
//		.fill (2048*4096) * MAX_VCPU_ENTRIES, 1, 0
//SVM NPT PT buffers
u8 g_svm_npt_pts_buffers[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAGE_SIZE_4K * MAX_VCPU_ENTRIES]__attribute__(( section(".palign_data") )); 

  //sipi pages for CPUs
//  .global svm_sipi_page_buffers
//  svm_sipi_page_buffers:
//    .fill 4096 * MAX_VCPU_ENTRIES, 1, 0
//SVM SIPI page buffers used for guest INIT-SIPI-SIPI emulation
u8 g_svm_sipi_page_buffers[PAGE_SIZE_4K * MAX_VCPU_ENTRIES]__attribute__(( section(".palign_data") ));

//  .global svm_hsave_buffers
//  svm_hsave_buffers:
//  .fill 8192 * MAX_VCPU_ENTRIES, 1, 0
//SVM VM_HSAVE buffers 
u8 g_svm_hsave_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES]__attribute__(( section(".palign_data") ));

  
//  .global svm_vmcb_buffers
//  svm_vmcb_buffers:
//  .fill 8192 * MAX_VCPU_ENTRIES, 1, 0
//SVM VMCB buffers 
u8 g_svm_vmcb_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES]__attribute__(( section(".palign_data") )); 

//  .global svm_iopm
//	svm_iopm:
//		.fill	SIZEOF_IOPM_BITMAP, 1, 0
//SVM IO bitmap buffer
u8 g_svm_iopm[SIZEOF_IOPM_BITMAP]__attribute__(( section(".palign_data") )); 

//  .global svm_msrpm
//  svm_msrpm:
//    .fill SIZEOF_MSRPM_BITMAP, 1, 0
//SVM MSR bitmap buffer
u8 g_svm_msrpm[SIZEOF_MSRPM_BITMAP]__attribute__(( section(".palign_data") ));


void runtime_globals_init(){

	//initialize runtime parameter block pointer
	rpb = (RPB *)_rpb;

}
 