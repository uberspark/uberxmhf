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

/*
 * guest CPU state uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_primesmp.h>
#include <geec_sentinel.h>
#include <xc_init.h>

//////
// data
//////

extern void __xmhf_exception_handler_0(void);
extern void __xmhf_exception_handler_1(void);
extern void __xmhf_exception_handler_2(void);
extern void __xmhf_exception_handler_3(void);
extern void __xmhf_exception_handler_4(void);
extern void __xmhf_exception_handler_5(void);
extern void __xmhf_exception_handler_6(void);
extern void __xmhf_exception_handler_7(void);
extern void __xmhf_exception_handler_8(void);
extern void __xmhf_exception_handler_9(void);
extern void __xmhf_exception_handler_10(void);
extern void __xmhf_exception_handler_11(void);
extern void __xmhf_exception_handler_12(void);
extern void __xmhf_exception_handler_13(void);
extern void __xmhf_exception_handler_14(void);
extern void __xmhf_exception_handler_15(void);
extern void __xmhf_exception_handler_16(void);
extern void __xmhf_exception_handler_17(void);
extern void __xmhf_exception_handler_18(void);
extern void __xmhf_exception_handler_19(void);
extern void __xmhf_exception_handler_20(void);
extern void __xmhf_exception_handler_21(void);
extern void __xmhf_exception_handler_22(void);
extern void __xmhf_exception_handler_23(void);
extern void __xmhf_exception_handler_24(void);
extern void __xmhf_exception_handler_25(void);
extern void __xmhf_exception_handler_26(void);
extern void __xmhf_exception_handler_27(void);
extern void __xmhf_exception_handler_28(void);
extern void __xmhf_exception_handler_29(void);
extern void __xmhf_exception_handler_30(void);
extern void __xmhf_exception_handler_31(void);

#define XMHF_EXCEPTION_HANDLER_ADDROF(vector) &__xmhf_exception_handler_##vector

u32  __xmhfhic_exceptionstubs[] = { XMHF_EXCEPTION_HANDLER_ADDROF(0),
							XMHF_EXCEPTION_HANDLER_ADDROF(1),
							XMHF_EXCEPTION_HANDLER_ADDROF(2),
							XMHF_EXCEPTION_HANDLER_ADDROF(3),
							XMHF_EXCEPTION_HANDLER_ADDROF(4),
							XMHF_EXCEPTION_HANDLER_ADDROF(5),
							XMHF_EXCEPTION_HANDLER_ADDROF(6),
							XMHF_EXCEPTION_HANDLER_ADDROF(7),
							XMHF_EXCEPTION_HANDLER_ADDROF(8),
							XMHF_EXCEPTION_HANDLER_ADDROF(9),
							XMHF_EXCEPTION_HANDLER_ADDROF(10),
							XMHF_EXCEPTION_HANDLER_ADDROF(11),
							XMHF_EXCEPTION_HANDLER_ADDROF(12),
							XMHF_EXCEPTION_HANDLER_ADDROF(13),
							XMHF_EXCEPTION_HANDLER_ADDROF(14),
							XMHF_EXCEPTION_HANDLER_ADDROF(15),
							XMHF_EXCEPTION_HANDLER_ADDROF(16),
							XMHF_EXCEPTION_HANDLER_ADDROF(17),
							XMHF_EXCEPTION_HANDLER_ADDROF(18),
							XMHF_EXCEPTION_HANDLER_ADDROF(19),
							XMHF_EXCEPTION_HANDLER_ADDROF(20),
							XMHF_EXCEPTION_HANDLER_ADDROF(21),
							XMHF_EXCEPTION_HANDLER_ADDROF(22),
							XMHF_EXCEPTION_HANDLER_ADDROF(23),
							XMHF_EXCEPTION_HANDLER_ADDROF(24),
							XMHF_EXCEPTION_HANDLER_ADDROF(25),
							XMHF_EXCEPTION_HANDLER_ADDROF(26),
							XMHF_EXCEPTION_HANDLER_ADDROF(27),
							XMHF_EXCEPTION_HANDLER_ADDROF(28),
							XMHF_EXCEPTION_HANDLER_ADDROF(29),
							XMHF_EXCEPTION_HANDLER_ADDROF(30),
							XMHF_EXCEPTION_HANDLER_ADDROF(31),
};

// CASM module supporting data structures

// initialization phase CPU stacks
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];


// following two data structures used for SMP bootup
__attribute__(( aligned(16) )) u64 _xcsmp_ap_init_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00af9b000000ffffULL,	//CPL-0 64-bit code descriptor (CS64)
	0x00af93000000ffffULL,	//CPL-0 64-bit data descriptor (DS/SS/ES/FS/GS)
};

__attribute__(( aligned(16) )) arch_x86_gdtdesc_t _xcsmp_ap_init_gdt  = {
	.size=sizeof(_xcsmp_ap_init_gdt_start)-1,
	.base=&_xcsmp_ap_init_gdt_start,
};



//static bool CASM_FUNCCALL(__xmhfhic_ap_entry,void) __attribute__((naked));
void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void);
static u64 _xcsmp_ap_entry_lock = 1;
static mtrr_state_t _mtrrs;
u64 _ap_cr3=0;


// GDT
__attribute__((section(".data"))) __attribute__(( aligned(16) )) u64 __xmhfhic_x86vmx_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00cf9a000000ffffULL,	//CPL-0 32-bit code descriptor (CS64)
	0x00cf92000000ffffULL,	//CPL-0 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS64)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS64)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x0000000000000000ULL,  //TSS descriptors (64-bits each)
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,

	0x0000000000000000ULL,
};
// GDT descriptor
__attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt  = {
	.size=sizeof(__xmhfhic_x86vmx_gdt_start)-1,
	.base=(u32)&__xmhfhic_x86vmx_gdt_start,
};


// TSS
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][PAGE_SIZE_4K] = { 0 };
// TSS stacks
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];


// IDT
__attribute__((section(".data"))) __attribute__(( aligned(16) )) idtentry_t __xmhfhic_x86vmx_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS] ;
// IDT descriptor
__attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_idtdesc_t __xmhfhic_x86vmx_idt = {
	.size=sizeof(__xmhfhic_x86vmx_idt_start)-1,
	.base=(u32)&__xmhfhic_x86vmx_idt_start,
};


// sysenter CPU stacks
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _geec_primesmp_sysenter_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];


__attribute__((section(".data"))) __attribute__(( aligned(4) )) u32 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID];

__attribute__((section(".data"))) __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];


