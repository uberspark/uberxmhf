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
 * XMHF core global data module (x86 common arch.)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf-core.h>
#include <xc-x86.h>

//bplt-x86-data

//VCPU structure for each "guest OS" core
//VCPU g_vcpubuffers[MAX_VCPU_ENTRIES] __attribute__(( section(".data") ));
VCPU g_bplt_vcpu[MAX_VCPU_ENTRIES] __attribute__(( section(".data") ));

//runtime TSS
u8 g_runtime_TSS[PAGE_SIZE_4K] __attribute__(( section(".data") ));

//signal that basic base platform data structure initialization is complete 
//(used by the exception handler component)
bool g_bplt_initiatialized __attribute__(( section(".data") )) = false;


//rntm-x86-data
//runtime GDT
u64 x_gdt_start[] __attribute__(( section(".data"), aligned(16) )) = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00cf9b000000ffffULL,	//CPL-0 code descriptor (CS)
	0x00cf93000000ffffULL,	//CPL-0 data descriptor (DS/SS/ES/FS/GS)
	0x00cffb000000ffffULL,	//CPL-3 code descriptor (CS)
	0x00cff3000000ffffULL,	//CPL-3 data descriptor (DS/SS/ES/FS/GS)
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
	.XtVmmEntryPoint= (u32)xmhf_runtime_entry,
	.XtGuestOSBootModuleBase= 0,
	.XtGuestOSBootModuleSize= 0, 
	.runtime_appmodule_base= 0,
	.runtime_appmodule_size= 0,
	.XtVmmStackBase= (u32)x_init_stack,
	.XtVmmStackSize= 8192,
	.XtVmmRuntimePhysBase= 0,
	.XtVmmRuntimeVirtBase= 0,
	.XtVmmRuntimeSize= 0,
	.XtVmmE820Buffer= (u32)g_e820map,
	.XtVmmE820NumEntries= 0,
	.XtVmmMPCpuinfoBuffer= (u32)g_cpumap,
	.XtVmmMPCpuinfoNumEntries= 0,
	.RtmUartConfig = {0},
	.isEarlyInit=1,					//1 for an "early init" else 0 (late-init)
};
 
/*
 * XMHF base platform SMP real mode trampoline
 * this is where all AP CPUs start executing when woken up
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

/*
	.code16
  .global _ap_bootstrap_start
  _ap_bootstrap_start:
    jmp ap_bootstrap_bypassdata
    .global _ap_cr3_value
    _ap_cr3_value:
      .long 0
    .global _ap_cr4_value
    _ap_cr4_value: 
      .long 0
    .global _ap_runtime_entrypoint
    _ap_runtime_entrypoint:
	  .long 0
    .align 16
    .global _mle_join_start
    _mle_join_start:
    .long _ap_gdt_end - _ap_gdt_start - 1 // gdt_limit
    .long _ap_gdt_start - _ap_bootstrap_start + 0x10000// gdt_base
    .long 0x00000008 // CS
    .long _ap_clear_pipe - _ap_bootstrap_start + 0x10000 // entry point
    _mle_join_end:
    
    _ap_gdtdesc:
      .word _ap_gdt_end - _ap_gdt_start - 1
      .long _ap_gdt_start - _ap_bootstrap_start + 0x10000  
    
    .align 16
    _ap_gdt_start:
      .quad 0x0000000000000000
      .quad 0x00cf9a000000ffff	
      .quad 0x00cf92000000ffff
    _ap_gdt_end:
      .word 0
    
    .align 16
  ap_bootstrap_bypassdata:
      movw $0x1000, %ax
    	movw %ax, %ds
    	movw %ax, %es
    	movw $0xFFFF, %sp
    	movw $0x4000, %ax
    	movw %ax, %ss
    	
    	movw $0x0020, %si

      lgdt (%si)

      movl %cr0, %eax
      orl $0x1, %eax
      movl %eax, %cr0

      jmpl $0x08, $(_ap_clear_pipe - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4))
    .code32
    _ap_clear_pipe:
      movw $0x10, %ax
      movw %ax, %ds
      movw %ax, %es
      movw %ax, %ss
      movw %ax, %fs
      movw %ax, %gs

             
      movl $(_ap_cr3_value - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4)), %esi
      movl (%esi), %ebx
      movl %ebx, %cr3
      movl $(_ap_cr4_value - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4)), %esi
      movl (%esi), %ebx
      movl %ebx, %cr4
      movl $(_ap_runtime_entrypoint - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4)), %esi
      movl (%esi), %ebx
      
      movl %cr0, %eax
      orl $0x80000000, %eax	
      movl %eax, %cr0

      jmpl *%ebx
      hlt
*/

u8 _ap_bootstrap_blob[256] = {
															//0x00: _ap_bootstrap_start
		0xeb, 0x4e, 										//0x00: jmp ap_bootstrap_bypassdata
		0x00, 0x00, 0x00, 0x00,								//0x02: _ap_cr3_value
		0x00, 0x00, 0x00, 0x00,								//0x06: _ap_cr4_value
		0x00, 0x00, 0x00, 0x00, 							//0x0a: _ap_runtime_entrypoint
		0x90, 0x90,											//.align 16
															//0x10: _mle_join_start
		0x17, 0x00, 0x00, 0x00,								//0x10: .long _ap_gdt_end - _ap_gdt_start - 1 // gdt_limit
		0x30, 0x00, 0x01, 0x00,								//0x14: .long _ap_gdt_start - _ap_bootstrap_start + 0x10000// gdt_base
		0x08, 0x00, 0x00, 0x00,								//0x18: .long 0x00000008 // CS
		0x77, 0x00, 0x01, 0x00, 							//0x1C: .long _ap_clear_pipe - _ap_bootstrap_start + 0x10000 // entry point
															//0x20: _ap_gdtdesc:
		0x17, 0x00,											//0x20: .word _ap_gdt_end - _ap_gdt_start - 1
		0x30, 0x00, 0x01, 0x00,								//0x22: .long _ap_gdt_start - _ap_bootstrap_start + 0x10000  
															//0x26: .align 16
		0x90, 0x90, 0x90, 0x90, 							//0x26: .align 16
		0x90, 0x90, 0x90, 0x90,								//0x29: .align 16
		0x90, 0x90,											//0x2d: .align 16
															//0x30:_ap_gdt_start:
		0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 	//0x30: .quad 0x0000000000000000
		0xff, 0xff, 0x00, 0x00, 0x00, 0x9a, 0xcf, 0x00, 	//0x38: .quad 0x00cf9a000000ffff	
		0xff, 0xff, 0x00, 0x00, 0x00, 0x92, 0xcf, 0x00, 	//0x40: .quad 0x00cf92000000ffff
															//0x48: _ap_gdt_end:
		0x00, 0x00,											//0x48: .word 0
															//0x4a: .align 16
		0x90, 0x90, 0x90, 0x90, 0x90, 0x90,					//0x4a: .align 16
															//0x50: _ap_bootstrap_bypassdata
		0xb8, 0x00, 0x10,									//0x50: mov    $0x1000,%ax
		0x8e, 0xd8,                							//0x53: mov    %ax,%ds
		0x8e, 0xc0,                							//0x55: mov    %ax,%es
		0xbc, 0xff, 0xff,          							//0x57: mov    $0xffff,%sp
		0xb8, 0x00, 0x40,          							//0x5a: mov    $0x4000,%ax
		0x8e, 0xd0,                							//0x5d: mov    %ax,%ss
		0xbe, 0x20, 0x00,          							//0x5f: mov    $0x20,%si
		0x0f, 0x01, 0x14,          							//0x62: lgdtw  (%si)
		0x0f, 0x20, 0xc0,          							//0x65: mov    %cr0,%eax
		0x66, 0x83, 0xc8, 0x01,    							//0x68: or     $0x1,%eax
		0x0f, 0x22, 0xc0,          							//0x6c: mov    %eax,%cr0
		0x66, 0xea, 0x77, 0x00, 0x01, 0x00, 0x08, 0x00,		//0x6f: jmpl $0x08, $(_ap_clear_pipe - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4))
															//0x77: _ap_clear_pipe:
		0x66, 0xb8, 0x10, 0x00,    							//0x77: mov    $0x10,%ax
		0x8e, 0xd8,                							//0x7b: mov    %eax,%ds
		0x8e, 0xc0,                							//0x7d: mov    %eax,%es
		0x8e, 0xd0,                							//0x7f: mov    %eax,%ss
		0x8e, 0xe0,                							//0x81: mov    %eax,%fs
		0x8e, 0xe8,                							//0x83: mov    %eax,%gs
		0xbe, 0x02, 0x00, 0x01, 0x00,						//0x85: movl $(_ap_cr3_value - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4)), %esi
		0x8b, 0x1e,                							//0x8a: mov    (%esi),%ebx
		0x0f, 0x22, 0xdb,          							//0x8c: mov    %ebx,%cr3
		0xbe, 0x06, 0x00, 0x01, 0x00,						//0x8f: movl $(_ap_cr4_value - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4)), %esi
		0x8b, 0x1e,                							//0x94: mov    (%esi),%ebx
		0x0f, 0x22, 0xe3,         							//0x96: mov    %ebx,%cr4
		0xbe, 0x0a, 0x00, 0x01, 0x00,						//0x99: movl $(_ap_runtime_entrypoint - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4)), %esi
		0x8b, 0x1e,                							//0x9e: mov    (%esi),%ebx
		0x0f, 0x20, 0xc0,          							//0xa0: mov    %cr0,%eax
		0x0d, 0x00, 0x00, 0x00, 0x80,						//0xa3: or     $0x80000000,%eax
		0x0f, 0x22, 0xc0,         							//0xa8: mov    %eax,%cr0
		0xff, 0xe3,              							//0xab: jmp    *%ebx
		0xf4,	                  							//0xad: hlt    

};

u32 * _ap_bootstrap_blob_cr3 = (u32 *) & _ap_bootstrap_blob[0x02];

u32 * _ap_bootstrap_blob_cr4 = (u32 *) &_ap_bootstrap_blob[0x06];

u32 * _ap_bootstrap_blob_runtime_entrypoint = (u32 *) &_ap_bootstrap_blob[0x0a];

u8 * _ap_bootstrap_blob_mle_join_start = (u8 *) &_ap_bootstrap_blob[0x10];


//xc-apihub

//hypapp PAE page tables
u64 hypapp_3level_pdpt[PAE_MAXPTRS_PER_PDPT] __attribute__(( section(".palign_data") ));
u64 hypapp_3level_pdt[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT] __attribute__(( section(".palign_data") ));

//core PAE page tables
u64 core_3level_pdpt[PAE_MAXPTRS_PER_PDPT] __attribute__(( section(".palign_data") ));
u64 core_3level_pdt[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT] __attribute__(( section(".palign_data") ));

//core and hypapp page table base address (PTBA)
u32 core_ptba=0;
u32 hypapp_ptba=0;

//xc-xcphandler

//core IDT
u64 xmhf_xcphandler_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS] __attribute__(( section(".data"), aligned(16) ));

//core IDT descriptor
arch_x86_idtdesc_t xmhf_xcphandler_idt __attribute__(( section(".data"), aligned(16) )) = {
	.size=sizeof(xmhf_xcphandler_idt_start)-1,
	.base=(u32)&xmhf_xcphandler_idt_start,
};
