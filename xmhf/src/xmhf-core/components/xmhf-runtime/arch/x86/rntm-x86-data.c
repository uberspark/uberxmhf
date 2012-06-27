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

/**
 * rntm-x86-data.c
 * EMHF runtime data definitions - x86 specific
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h> 

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


RPB arch_rpb __attribute__(( section(".s_rpb") )) = {
	.magic= RUNTIME_PARAMETER_BLOCK_MAGIC,
	.XtVmmEntryPoint= (u32)emhf_runtime_entry,
	.XtVmmPdptBase= (u32)x_3level_pdpt,
	.XtVmmPdtsBase= (u32)x_3level_pdt,
	//.XtVmmNpdtBase= 0,
	//.XtVmmNestedNpdtBase= 0,
	.XtGuestOSBootModuleBase= 0,
	.XtGuestOSBootModuleSize= 0, 
	.runtime_appmodule_base= 0,
	.runtime_appmodule_size= 0,
	.XtVmmStackBase= (u32)x_init_stack,
	.XtVmmStackSize= 8192,
	.XtVmmGdt= (u32)&x_gdt,
	//.XtVmmNetworkAdapterStructureBase= 0,
	//.XtVmmHsaveBase= 0,
	//.XtVmmVMCBBase= 0,
	//.XtVmmIopmBase= 0,
	//.XtVmmNestedPdptBase= 0,
	//.XtVmmNestedPdtsBase= 0,
	//.XtVmmNestedPtsBase= 0,
	.XtVmmIdt= (u32)emhf_xcphandler_idt,
	.XtVmmIdtFunctionPointers= (u32)emhf_xcphandler_exceptionstubs,
	.XtVmmIdtEntries= 32,
	//.XtVmmE1000DescBase= 0,
	//.XtVmmE1000HeaderBase= 0,
	//.XtVmmE1000BodyBase= 0,
	.XtVmmRuntimePhysBase= 0,
	.XtVmmRuntimeVirtBase= 0,
	.XtVmmRuntimeSize= 0,
	.XtVmmE820Buffer= (u32)g_e820map,
	.XtVmmE820NumEntries= 0,
	.XtVmmMPCpuinfoBuffer= (u32)g_cpumap,
	.XtVmmMPCpuinfoNumEntries= 0,
	.XtVmmTSSBase= (u32)g_runtime_TSS,
	//.RtmSVMDevBitmapBase= (u32)g_svm_dev_bitmap,
	//.RtmVMXVTdPdpt= (u32)g_vmx_vtd_pdp_table,
	//.RtmVMXVTdPdts= (u32)g_vmx_vtd_pd_tables,
	//.RtmVMXVTdPts= (u32)g_vmx_vtd_p_tables,
	//.RtmVMXVTdRET= (u32)g_vmx_vtd_ret,
	//.RtmVMXVTdCET= (u32)g_vmx_vtd_cet,
	//.uart_config=(u32)&g_uart_config,
	.isEarlyInit=1,					//1 for an "early init" else 0 (late-init)
};
 
