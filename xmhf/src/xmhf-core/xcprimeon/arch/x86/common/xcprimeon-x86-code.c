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
 * sl-x86.c
 * EMHF secure loader x86 arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
#include <xmhf.h>
//#include <xmhf-sl.h>

#include <xcprimeon.h>

#include "cpu/x86/include/common/_processor.h"  	//CPU
#include "cpu/x86/include/common/_paging.h"     	//MMU
#include "platform/x86pc/include/common/_acpi.h"			//ACPI glue
#include "platform/x86pc/include/common/_memaccess.h"	//platform memory access

//we only have confidence in the runtime's expected value here in the SL
//static INTEGRITY_MEASUREMENT_VALUES g_sl_gold /* __attribute__(( section("") )) */ = {
//    .sha_runtime = ___RUNTIME_INTEGRITY_HASH___,
//    .sha_slabove64K = BAD_INTEGRITY_HASH,
//    .sha_slbelow64K = BAD_INTEGRITY_HASH
//};


/* XXX TODO Read PCR values and sanity-check that DRTM was successful
 * (i.e., measurements match expectations), and integrity-check the
 * runtime. */
/* Note: calling this *before* paging is enabled is important. */
/*bool xmhf_sl_arch_integrity_check(u8* runtime_base_addr, size_t runtime_len) {
    int ret;
    u32 locality = EMHF_TPM_LOCALITY_PREF; 
    tpm_pcr_value_t pcr17, pcr18;    
	(void)g_sl_gold;

    print_hex("SL: Golden Runtime SHA-1: ", g_sl_gold.sha_runtime, SHA_DIGEST_LENGTH);

    printf("\nSL: CR0 %08lx, CD bit %ld", read_cr0(), read_cr0() & CR0_CD);
    hashandprint("SL: Computed Runtime SHA-1: ",
                 runtime_base_addr, runtime_len);    

    if(xmhf_tpm_open_locality(locality)) {
        printf("SL: FAILED to open TPM locality %d\n", locality);
        return false;
    }
    
    if((ret = tpm_pcr_read(locality, 17, &pcr17)) != TPM_SUCCESS) {
        printf("TPM: ERROR: tpm_pcr_read FAILED with error code 0x%08x\n", ret);
        return false;
    }
    print_hex("PCR-17: ", &pcr17, sizeof(pcr17));

    if((ret = tpm_pcr_read(locality, 18, &pcr18)) != TPM_SUCCESS) {
        printf("TPM: ERROR: tpm_pcr_read FAILED with error code 0x%08x\n", ret);
        return false;
    }
    print_hex("PCR-18: ", &pcr18, sizeof(pcr18));    

    // free TPM so that OS driver works as expected 
    xmhf_tpm_arch_deactivate_all_localities();
    
    return true;    
}
*/

void xmhf_sl_arch_x86_invoke_runtime_entrypoint(u32 entrypoint, u32 stacktop) {
		
	asm volatile(
		"movl %0, %%esp \r\n"
		"movl %1, %%eax \r\n"
		"jmpl *%%eax \r\n"
		: //no outputs
		: "m" (stacktop), "m" (entrypoint)
		: "eax", "esp"
	);
		
		
} 

void xmhf_sl_arch_xfer_control_to_runtime(XMHF_BOOTINFO *xcbootinfo){
	u32 ptba;	//page table base address

	printf("Transferring control to runtime\n");

	#ifndef __XMHF_VERIFICATION__
	//transfer control to runtime and never return
	xmhf_sl_arch_x86_invoke_runtime_entrypoint(xcbootinfo->entrypoint, (xcbootinfo->stack_base+xcbootinfo->stack_size));
	#else
	return;
	#endif
}

void xmhf_sl_arch_baseplatform_initialize(void){
	
	//initialize PCI subsystem
	xmhf_baseplatform_arch_x86_pci_initialize();
	
	//check ACPI subsystem
	{
		ACPI_RSDP rsdp;
		#ifndef __XMHF_VERIFICATION__
			//TODO: plug in a BIOS data area map/model
			if(!xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp)){
				printf("\n%s: ACPI RSDP not found, Halting!", __FUNCTION__);
				HALT();
			}
		#endif //__XMHF_VERIFICATION__
	}
	
}

//get CPU vendor
u32 xmhf_baseplatform_arch_x86_getcpuvendor(void){
	u32 vendor_dword1, vendor_dword2, vendor_dword3;
	u32 cpu_vendor;
	asm(	"xor	%%eax, %%eax \n"
				  "cpuid \n"		
				  "mov	%%ebx, %0 \n"
				  "mov	%%edx, %1 \n"
				  "mov	%%ecx, %2 \n"
			     :	//no inputs
					 : "m"(vendor_dword1), "m"(vendor_dword2), "m"(vendor_dword3)
					 : "eax", "ebx", "ecx", "edx" );

	if(vendor_dword1 == AMD_STRING_DWORD1 && vendor_dword2 == AMD_STRING_DWORD2
			&& vendor_dword3 == AMD_STRING_DWORD3)
		cpu_vendor = CPU_VENDOR_AMD;
	else if(vendor_dword1 == INTEL_STRING_DWORD1 && vendor_dword2 == INTEL_STRING_DWORD2
			&& vendor_dword3 == INTEL_STRING_DWORD3)
		cpu_vendor = CPU_VENDOR_INTEL;
	else{
		printf("\n%s: unrecognized x86 CPU (0x%08x:0x%08x:0x%08x). HALT!",
			__FUNCTION__, vendor_dword1, vendor_dword2, vendor_dword3);
		HALT();
	}   	 	

	return cpu_vendor;
}

//initialize GDT
void xmhf_baseplatform_arch_x86_initializeGDT(void){
	
	asm volatile(
		"lgdt  %0 \r\n"
		"pushl	%1 \r\n"				// far jump to runtime entry point
		"pushl	$reloadsegs \r\n"
		"lret \r\n"
		"reloadsegs: \r\n"
		"movw	%2, %%ax \r\n"
		"movw	%%ax, %%ds \r\n"	
		"movw	%%ax, %%es \r\n"
		"movw	%%ax, %%fs \r\n"
		"movw	%%ax, %%gs \r\n"
		"movw  %%ax, %%ss \r\n"
		: //no outputs
		: "m" (_gdt), "i" (__CS_CPL0), "i" (__DS_CPL0)
		: //no clobber
	);

	
}

//initialize IO privilege level
void xmhf_baseplatform_arch_x86_initializeIOPL(void){
	
	asm volatile(
		"pushl	$0x3000 \r\n"					// clear flags, but set IOPL=3 (CPL-3)
		"popf \r\n"
		: //no outputs
		: //no inputs
		: //no clobber
	);
	
	
}

//initialize TR/TSS
void xmhf_baseplatform_arch_x86_initializeTSS(void){
		u32 i;
		u32 tss_base=(u32)&_tss;
		TSSENTRY *t;
		tss_t *tss= (tss_t *)_tss;
		
		tss->ss0 = __DS_CPL0;
		tss->esp0 = (u32)_slab_table[XMHF_SLAB_XCEXHUB_INDEX].slab_tos;

		printf("\nfixing TSS descriptor (TSS base=%x)...", tss_base);
		t= (TSSENTRY *)(u32)&_gdt_start[(__TRSEL/sizeof(u64))];
		t->attributes1= 0xE9;
		t->limit16_19attributes2= 0x0;
		t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);      
		t->limit0_15=0x67;
		printf("\nTSS descriptor fixed.");

}


//=========================================================================================
//--------------------------------------------------------------------------------------
//bootstrap exception handling without SMP support
//only designed until real SMP exception handler slab (xcexhub) can take control

__attribute__((section(".libxmhfdebugdata"))) __attribute__(( aligned(4096) )) static u8 _xcinitbs_exception_stack[PAGE_SIZE_4K];
__attribute__((section(".libxmhfdebugdata"))) __attribute__(( aligned(4096) )) static u32 _xcinitbs_exception_stack_index = &_xcinitbs_exception_stack + PAGE_SIZE_4K;

#define XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(vector) 												\
	__attribute__(( section(".slab_trampoline") )) static void __xcinitbs_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
						"xchg   %0, %%esp \r\n"						\
						"pushal \r\n"								\
						"pushl %%esp \r\n"							\
						"pushl  %0 \r\n"							\
						"movl %%cr3, %%ebx \r\n"					\
						"pushl %%ebx		\r\n"					\
						"movl	%1, %%ebx\r\n"						\
						"movl	%%ebx, %%cr3\r\n"					\
						"pushl	%2\r\n" 							\
						"call	xmhf_xcinitbs_xcphandler_arch_hub\r\n"		\
						"addl $4, %%esp \r\n"						\
						"popl %%ebx \r\n"							\
						"movl  %%ebx, %%cr3 \r\n"					\
						"addl $8, %%esp \r\n"						\
						"popal \r\n"								\
						"xchg	%0, %%esp \r\n"						\
						"iretl \r\n"								\
					:												\
					:	"m" (_xcinitbs_exception_stack_index), "m" (_slab_table[XMHF_SLAB_INITBS_INDEX].slab_macmid), "i" (vector)				\
		);															\
	}\


#define XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(vector) &__xcinitbs_exception_handler_##vector

XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(0)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(1)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(2)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(3)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(4)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(5)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(6)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(7)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(8)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(9)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(10)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(11)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(12)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(13)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(14)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(15)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(16)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(17)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(18)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(19)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(20)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(21)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(22)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(23)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(24)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(25)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(26)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(27)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(28)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(29)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(30)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(31)
	
static u32 __xcinitbs_exceptionstubs[] = { 	XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(0),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(1),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(2),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(3),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(4),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(5),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(6),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(7),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(8),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(9),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(10),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(11),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(12),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(13),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(14),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(15),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(16),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(17),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(18),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(19),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(20),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(21),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(22),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(23),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(24),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(25),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(26),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(27),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(28),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(29),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(30),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(31),
};


//initialize basic exception handling
void _xcprimeon_initialize_exceptionhandling(void){
	u32 *pexceptionstubs;
	u32 i;

	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		idtentry_t *idtentry=(idtentry_t *)((u32)&_idt_start+ (i*8));
		idtentry->isrLow= (u16)__xcinitbs_exceptionstubs[i];
		idtentry->isrHigh= (u16) ( (u32)__xcinitbs_exceptionstubs[i] >> 16 );
		idtentry->isrSelector = __CS_CPL0;
		idtentry->count=0x0;
		idtentry->type=0xEE;	//32-bit interrupt gate
								//present=1, DPL=11b, system=0, type=1110b
	}

	//load IDT
	asm volatile(
		"lidt  %0 \r\n"
		: //no outputs
		: "m" (_idt)
		: //no clobber
	);
}
					

__attribute__(( section(".slab_trampoline") )) static void _xcprimeon_xcphandler_arch_unhandled(u32 vector, u32 orig_cr3, u32 orig_esp, struct regs *r){
	u32 exception_cs, exception_eip, exception_eflags, errorcode=0;

	if(vector == CPU_EXCEPTION_DF ||
		vector == CPU_EXCEPTION_TS ||
		vector == CPU_EXCEPTION_NP ||
		vector == CPU_EXCEPTION_SS ||
		vector == CPU_EXCEPTION_GP ||
		vector == CPU_EXCEPTION_PF ||
		vector == CPU_EXCEPTION_AC){
		errorcode = *(uint32_t *)(orig_esp+0);
		orig_esp += sizeof(uint32_t);	//skip error code on stack if applicable
	}

	exception_eip = *(uint32_t *)(orig_esp+0);
	exception_cs = *(uint32_t *)(orig_esp+sizeof(uint32_t));
	exception_eflags = *(uint32_t *)(orig_esp+(2*sizeof(uint32_t)));

	printf("\nunhandled exception %x, halting!", vector);
	printf("\nstate dump follows...");
	//things to dump
	printf("\nCS:EIP 0x%04x:0x%08x with EFLAGS=0x%08x, errorcode=%08x", (u16)exception_cs, exception_eip, exception_eflags, errorcode);
	printf("\nCR0=%08x, CR2=%08x, CR3=%08x, CR4=%08x", read_cr0(), read_cr2(), orig_cr3, read_cr4());
	printf("\nEAX=0x%08x EBX=0x%08x ECX=0x%08x EDX=0x%08x", r->eax, r->ebx, r->ecx, r->edx);
	printf("\nESI=0x%08x EDI=0x%08x EBP=0x%08x ESP=0x%08x", r->esi, r->edi, r->ebp, orig_esp);
	printf("\nCS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x", (u16)read_segreg_cs(), (u16)read_segreg_ds(), (u16)read_segreg_es(), (u16)read_segreg_ss());
	printf("\nFS=0x%04x, GS=0x%04x", (u16)read_segreg_fs(), (u16)read_segreg_gs());
	printf("\nTR=0x%04x", (u16)read_tr_sel());

	//do a stack dump in the hopes of getting more info.
	{
		uint32_t i;
		uint32_t stack_start = orig_esp;
		printf("\n-----stack dump (16 entries)-----");
		for(i=stack_start; i < stack_start+(16*sizeof(uint32_t)); i+=sizeof(uint32_t)){
			printf("\nStack(0x%08x) -> 0x%08x", i, *(uint32_t *)i);
		}
		printf("\n-----end------------");
	}
}

//exception handler hub
__attribute__(( section(".slab_trampoline") )) void _xcprimeon_xcphandler_arch_hub(u32 vector, u32 orig_cr3, u32 orig_esp, struct regs *r){
	
	switch(vector){
		case 0x3:
			_xcprimeon_xcphandler_arch_unhandled(vector, orig_cr3, orig_esp, r);
			printf("Int3 dbgprint -- continue\n");
			break;
		
		default:
			_xcprimeon_xcphandler_arch_unhandled(vector, orig_cr3, orig_esp, r);
			printf("\nHalting System!\n");
			HALT();
	}
	
}



