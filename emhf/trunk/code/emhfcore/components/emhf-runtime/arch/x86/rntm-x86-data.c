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
 * rntm-x86-data.c
 * EMHF runtime data definitions - x86 specific
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <emhf.h> 

//runtime GDT
u64 x_gdt_start[] __attribute__(( section(".data"), aligned(16) )) = {
	0x0000000000000000ULL,
	0x00cf9a000000ffffULL,	
	0x00cf92000000ffffULL,	
	0x0000000000000000ULL	
};

//runtime GDT descriptor
arch_x86_gdtdesc_t x_gdt __attribute__(( section(".data"), aligned(16) )) = {
	.size=sizeof(x_gdt_start)-1,
	.base=(u32)&x_gdt_start,
};


//runtime PAE page tables
u8 x_3level_pdpt[PAGE_SIZE_4K] __attribute__(( section(".palign_data") ));
u8 x_3level_pdt[PAE_PTRS_PER_PDPT * PAGE_SIZE_4K] __attribute__(( section(".palign_data") ));
		
//runtime stack
u8 x_init_stack[RUNTIME_STACK_SIZE] __attribute__(( section(".stack") ));


/*
 * 
 
 //NOTE: The declaration here _MUST_ match definition of RPB in runtimesup.S	
typedef struct {
	u32 magic;
	u32 XtVmmEntryPoint;
	u32 XtVmmPdptBase;
	u32 XtVmmPdtsBase;
	u32 XtVmmNpdtBase;
	u32 XtVmmNestedNpdtBase;
	u32 XtGuestOSBootModuleBase;
	u32 XtGuestOSBootModuleSize;
	u32 XtGuestOSBootModuleBaseSup1;
	u32 XtGuestOSBootModuleSizeSup1;
	u32 XtVmmStackBase;
	u32 XtVmmStackSize;
	u32 XtVmmGdt;
	u32 XtVmmNetworkAdapterStructureBase;
	u32 XtVmmHsaveBase;
	u32 XtVmmVMCBBase;
	u32 XtVmmIopmBase;
	u32 XtVmmNestedPdptBase;
	u32 XtVmmNestedPdtsBase;
	u32 XtVmmNestedPtsBase;
	u32 XtVmmIdt;
	u32 XtVmmIdtFunctionPointers;
	u32 XtVmmIdtEntries;
	u32 XtVmmE1000DescBase;
	u32 XtVmmE1000HeaderBase;
	u32 XtVmmE1000BodyBase;
	u32 XtVmmRuntimePhysBase;
	u32 XtVmmRuntimeVirtBase;
	u32 XtVmmRuntimeSize;
	u32 XtVmmE820Buffer;
	u32 XtVmmE820NumEntries;
	u32 XtVmmMPCpuinfoBuffer;
	u32 XtVmmMPCpuinfoNumEntries;
	u32 XtVmmTSSBase;
	u32 RtmSVMDevBitmapBase;
	u32 RtmVMXVTdPdpt;
	u32 RtmVMXVTdPdts;
	u32 RtmVMXVTdPts;
	u32 RtmVMXVTdRET;
	u32 RtmVMXVTdCET;
    uart_config_t uart_config;	        // runtime options parsed in init and passed forward 
	u32 isEarlyInit;					//1 for an "early init" else 0 (late-init)
} __attribute__((packed)) RPB, *PRPB;

 
*/
 


/*


//------------------------------------------------------------------------------
//RUNTIME PARAMETER BLOCK DATA
//------------------------------------------------------------------------------
//NOTE: The definition here _MUST_ match declaration of RPB in target.h	
	.section .s_rpb
	.global _rpb
_rpb:
	.long RUNTIME_PARAMETER_BLOCK_MAGIC
	.long cstartup
	.long x_3level_pdpt
	.long	x_3level_pdt
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long x_init_stack
	.long 8192
	.long x_gdt
	.long 0 //.extern nwadapterstructure
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long emhf_xcphandler_idt
	.long emhf_xcphandler_exceptionstubs
	.long 32
	.long 0 //x_e1000desc
	.long 0 //x_e1000header
	.long 0 //x_e1000body
	.long 0  //physical base address of runtime
	.long 0  //virtual base address of runtime
	.long 0  //2M aligned size of runtime
	.long g_e820map				   //system E820 map
	.long 0                  //number of entries
	.long g_cpumap		       //system CPU map
	.long 0                  //number of entries
	.long g_runtime_TSS			 //runtime TSS
	.long	g_svm_dev_bitmap	 //runtime SVM DEV bitmap
	.long g_vmx_vtd_pdp_table	//runtime VMX(VT-d) DMA protection page-tables
	.long g_vmx_vtd_pd_tables
	.long g_vmx_vtd_p_tables
	.long g_vmx_vtd_ret				//runtime VMX(VT-d) DMA protection Root Entry Table
	.long g_vmx_vtd_cet				//runtime VMX(VT-d) DMA protection Context Entry Table 
	.long 0, 0, 0, 0				//32 bytes for field uart_config of type uart_config_t 
	.long 1							//isEarlyInit, 1 = early init, 0 = late init (default to early init)





*/
