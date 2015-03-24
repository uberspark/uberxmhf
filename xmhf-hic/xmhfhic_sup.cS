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

#include <xmhf.h>
#include <xmhf-hic.h>
#include <xmhf-debug.h>

// XMHF HIC prime assembly language code blobs
// author: amit vasudevan (amitvasudevan@acm.org)


// initialization phase CPU stacks
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) static u8 _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];


// following two data structures used for SMP bootup
__attribute__(( aligned(16) )) static u64 _xcsmp_ap_init_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00af9b000000ffffULL,	//CPL-0 64-bit code descriptor (CS64)
	0x00af93000000ffffULL,	//CPL-0 64-bit data descriptor (DS/SS/ES/FS/GS)
};

__attribute__(( aligned(16) )) static arch_x86_gdtdesc_t _xcsmp_ap_init_gdt  = {
	.size=sizeof(_xcsmp_ap_init_gdt_start)-1,
	.base=&_xcsmp_ap_init_gdt_start,
};


__attribute__((naked)) __attribute__ ((section(".hic_entrystub"))) __attribute__(( align(4096) )) void xcprimeon_arch_entry(void) {

	asm volatile ("movw %ds, %ax \r\n");
    asm volatile ("movw %ax, %es \r\n");
    asm volatile ("movw %ax, %fs \r\n");
    asm volatile ("movw %ax, %gs \r\n");
    asm volatile ("movw %ax, %ss \r\n");
    asm volatile ("movl $_init_cpustacks, %eax \r\n");
    asm volatile ("addl $16384, %eax \r\n");
    asm volatile ("movl %eax, %esp \r\n");
    asm volatile ("call slab_main \r\n");
    asm volatile ("hlt \r\n");

}


__attribute__((naked)) void _ap_bootstrap_code(void) {

    asm volatile (
           " .code32 \r\n"
           " movw %0, %%ax \r\n"
           " movw %%ax, %%ds \r\n"

           " movl %1, %%eax \r\n"
           " movl (%%eax), %%eax \r\n"

           " movl %2, %%ebx \r\n"
           " movl (%%ebx), %%ebx \r\n"

           " movl %3, %%edi \r\n"
           " movl (%%edi), %%edi \r\n"

           " jmpl *%%eax \r\n"
           " hlt \r\n"
           " .balign 4096 \r\n"
            :
            : "i" (__DS_CPL0),
              "i" ((X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_entrypoint)),
              "i" ((X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_cr3)),
              "i" ((X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, cpuidtable))
            :

        );



}


//
//XXX: globals:
//_ap_cr3
//void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void);
//__xmhfhic_x86vmx_cpuidtable
bool __xmhfhic_ap_entry(void) __attribute__((naked)){
    extern u64 _ap_cr3;

/*    //TODO: x86_64 --> x86
    asm volatile(
                    ".code32 \r\n"
					"_xcsmp_ap_start: \r\n"

					"movw %%ds, %%ax \r\n"
					"movw %%ax, %%es \r\n"
					"movw %%ax, %%fs \r\n"
					"movw %%ax, %%gs \r\n"
					"movw %%ax, %%ss \r\n"

    				"movl %%cr4, %%eax \r\n"
   					"orl $0x00000030, %%eax \r\n"
   					"movl %%eax, %%cr4 \r\n"

                    //"movl %0, %%ebx \r\n"
                    //"movl (%%ebx), %%ebx \r\n"
                    "movl %%ebx, %%cr3 \r\n"

                    "movl $0xc0000080, %%ecx \r\n"
                    "rdmsr \r\n"
                    "orl $0x00000100, %%eax \r\n"
                    "orl $0x00000800, %%eax \r\n"
                    "wrmsr \r\n"

                    "movl %%cr0, %%eax \r\n"
                    "orl $0x80000015, %%eax \r\n"
                    "movl %%eax, %%cr0 \r\n"

                    "movl %1, %%esi \r\n"
                    "lgdt (%%esi) \r\n"

                    "ljmp $8, $_xcsmp_ap_start64 \r\n"

                    ".code64 \r\n"
                    "_xcsmp_ap_start64: \r\n"

					"movw $0x10, %%ax \r\n"
					"movw %%ax, %%fs \r\n"
					"movw %%ax, %%gs \r\n"
					"movw %%ax, %%ss \r\n"
					"movw %%ax, %%ds \r\n"
					"movw %%ax, %%es \r\n"

                    "movl %2, %%ecx \r\n"
                    "rdmsr \r\n"
                    "andl $0x00000FFF, %%eax \r\n"
                    "orl %3, %%eax \r\n"
                    "wrmsr \r\n"

					:
					:   "i" (0), //unused
                        "i" (&_xcsmp_ap_init_gdt),
                        "i" (MSR_APIC_BASE),
                        "i" (X86SMP_LAPIC_MEMORYADDRESS)
	);



    asm volatile(
                 	"xorq %%rax, %%rax \r\n"                //RAX=0
                 	"movl %0, %%eax\r\n"                    //
					"movl (%%eax), %%eax\r\n"               //RAX(bits 0-7)=LAPIC ID
					"shr $24, %%eax\r\n"                    //RAX=LAPIC ID
                    //"movq %1, %%rbx \r\n"                   //RBX=&__xmhfhic_x86vmx_cpuidtable

                    "xorq %%rbx, %%rbx \r\n"
                    "movl %%edi, %%ebx \r\n"                   //RBX=&__xmhfhic_x86vmx_cpuidtable

                    "movq (%%rbx, %%rax, 8), %%rax \r\n"    //EAX= 0-based cpu index for the CPU

					"movl %2, %%ecx \r\n"					// ecx = sizeof(_cpustack[0])
					"mull %%ecx \r\n"						// eax = sizeof(_cpustack[0]) * eax
					"addl %%ecx, %%eax \r\n"				// eax = (sizeof(_cpustack[0]) * eax) + sizeof(_cpustack[0])
					"addl %3, %%eax \r\n"				    // eax = &_cpustack + (sizeof(_cpustack[0]) * eax) + sizeof(_cpustack[0])
					"movl %%eax, %%esp \r\n"				// esp = top of stack for the cpu

                    "jmp __xmhfhic_smp_cpu_x86_smpinitialize_commonstart \r\n"

					:
					:   "i" (X86SMP_LAPIC_ID_MEMORYADDRESS),
                        "i" (0), //unused
                        "i" (sizeof(_init_cpustacks[0])),
                        "i" (&_init_cpustacks)

                    :
	);
*/



    asm volatile(
                    ".code32 \r\n"
					"_xcsmp_ap_start: \r\n"

					"movw %%ds, %%ax \r\n"
					"movw %%ax, %%es \r\n"
					"movw %%ax, %%fs \r\n"
					"movw %%ax, %%gs \r\n"
					"movw %%ax, %%ss \r\n"

    				"movl %%cr4, %%eax \r\n"
   					"orl $0x00000030, %%eax \r\n"
   					"movl %%eax, %%cr4 \r\n"

                    "movl %%ebx, %%cr3 \r\n"

                    "movl $0xc0000080, %%ecx \r\n"
                    "rdmsr \r\n"
                    "orl $0x00000800, %%eax \r\n"
                    "wrmsr \r\n"

                    "movl %%cr0, %%eax \r\n"
                    "orl $0x80000015, %%eax \r\n"
                    "movl %%eax, %%cr0 \r\n"

                    //TODO: for non-TXT wakeup we need to reload GDT
                    //"movl %1, %%esi \r\n"
                    //"lgdt (%%esi) \r\n"

                    "movl %2, %%ecx \r\n"
                    "rdmsr \r\n"
                    "andl $0x00000FFF, %%eax \r\n"
                    "orl %3, %%eax \r\n"
                    "wrmsr \r\n"

					:
					:   "i" (0), //unused
                        "i" (0), //unused
                        "i" (MSR_APIC_BASE),
                        "i" (X86SMP_LAPIC_MEMORYADDRESS)
	);



    asm volatile(   ".code32 \r\n"
                 	"xorl %%eax, %%eax \r\n"                //EAX=0
                 	"movl %0, %%eax\r\n"                    //EAX=X86SMP_LAPIC_ID_MEMORYADDRESS
					"movl (%%eax), %%eax\r\n"               //EAX(bits 0-7)=LAPIC ID
					"shr $24, %%eax\r\n"                    //EAX=LAPIC ID

                    "xorl %%ebx, %%ebx \r\n"                //EBX=0
                    "movl %%edi, %%ebx \r\n"                //EBX=&__xmhfhic_x86vmx_cpuidtable

                    "movl (%%ebx, %%eax, 4), %%eax \r\n"    //EAX= 0-based cpu index for the CPU

					"movl %2, %%ecx \r\n"					//ecx = sizeof(_cpustack[0])
					"mull %%ecx \r\n"						//eax = sizeof(_cpustack[0]) * eax
					"addl %%ecx, %%eax \r\n"				//eax = (sizeof(_cpustack[0]) * eax) + sizeof(_cpustack[0])
					"addl %3, %%eax \r\n"				    //eax = &_cpustack + (sizeof(_cpustack[0]) * eax) + sizeof(_cpustack[0])
					"movl %%eax, %%esp \r\n"				//esp = top of stack for the cpu

                    "jmp __xmhfhic_smp_cpu_x86_smpinitialize_commonstart \r\n"

					:
					:   "i" (X86SMP_LAPIC_ID_MEMORYADDRESS),
                        "i" (0), //unused
                        "i" (sizeof(_init_cpustacks[0])),
                        "i" (&_init_cpustacks)

                    :
	);


}



























//////////////////////////////////////////////////////////////////////////////
// setup cpu state for hic



//load GDT and initialize segment registers
void __xmhfhic_x86vmx_loadGDT(arch_x86_gdtdesc_t *gdt_addr){

    xmhfhw_cpu_loadGDT(gdt_addr);

	asm volatile(
		"pushl	%0 \r\n"				// far jump to reload CS
		"pushl	$reloadsegs \r\n"
		"lret \r\n"
		"reloadsegs: \r\n"
		"movw	%1, %%ax \r\n"
		"movw	%%ax, %%ds \r\n"
		"movw	%%ax, %%es \r\n"
		"movw	%%ax, %%fs \r\n"
		"movw	%%ax, %%gs \r\n"
		"movw   %%ax, %%ss \r\n"
		: //no outputs
		: "i" (__CS_CPL0), "i" (__DS_CPL0)
		: "eax"
	);


}




//set IOPl to CPl-3
void __xmhfhic_x86vmx_setIOPL3(u64 cpuid){

	asm volatile(
        "pushfl \r\n"
        "popl %%eax \r\n"
		"orl $0x3000, %%eax \r\n"					// clear flags, but set IOPL=3 (CPL-3)
		"pushl %%eax \r\n"
		"popfl \r\n"
		: //no outputs
		: //no inputs
		: "eax", "cc"
	);

}















































































#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
                        "pushl %0 \r\n"\
                        "pushal \r\n" \
                        "pushl %%esp \r\n" \
                        "call __xmhfhic_rtm_exception_stub\r\n"\
                        "addl $0x4, %%esp \r\n" \
                        "popal \r\n" \
                        "addl $0x08, %%esp \r\n" \
                        "iretl \r\n" \
					: \
					: "i" (vector) \
                    : \
               		);	\
    }\

#define XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(vector) 												\
	static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
                        "pushl $0x0 \r\n" \
                        "pushl %0 \r\n"\
                        "pushal \r\n" \
                        "pushl %%esp \r\n" \
                        "call __xmhfhic_rtm_exception_stub\r\n"\
                        "addl $0x4, %%esp \r\n" \
                        "popal \r\n" \
                        "addl $0x08, %%esp \r\n" \
                        "iretl \r\n" \
					: \
					: "i" (vector) \
                    : \
               		);	\
    }\


#define XMHF_EXCEPTION_HANDLER_ADDROF(vector) &__xmhf_exception_handler_##vector

XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(0)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(1)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(2)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(3)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(4)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(5)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(6)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(7)
XMHF_EXCEPTION_HANDLER_DEFINE(8)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(9)
XMHF_EXCEPTION_HANDLER_DEFINE(10)
XMHF_EXCEPTION_HANDLER_DEFINE(11)
XMHF_EXCEPTION_HANDLER_DEFINE(12)
XMHF_EXCEPTION_HANDLER_DEFINE(13)
XMHF_EXCEPTION_HANDLER_DEFINE(14)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(15)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(16)
XMHF_EXCEPTION_HANDLER_DEFINE(17)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(18)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(19)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(20)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(21)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(22)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(23)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(24)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(25)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(26)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(27)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(28)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(29)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(30)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(31)


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














//HIC runtime intercept stub
//__attribute__((naked)) void __xmhfhic_rtm_intercept_stub(void){
__attribute__((naked)) void __xmhfhic_rtm_intercept_stub(void){

    asm volatile ("pushal \r\n");
    asm volatile ("pushl %esp \r\n");
    asm volatile ("call __xmhfhic_rtm_intercept \r\n");
    asm volatile ("addl $0x4, %esp \r\n");
    asm volatile ("popal \r\n");
    asm volatile ("vmresume \r\n");
    asm volatile ("hlt \r\n");
}








//////

/////////////////////////////////////////////////////////////////////////////
// relinquish HIC initialization and move on to the first slab

void xmhfhic_arch_relinquish_control_to_init_slab(u64 cpuid, u64 entrystub, u64 mempgtbl_cr3, u64 slabtos){

/*
    //TODO: x86_64 --> x86
    //switch page tables to init slab pagetables
    asm volatile(
         "movq %0, %%rax \r\n"
         "movq %%rax, %%cr3 \r\n"
        :
        : "m" (mempgtbl_cr3)
        : "rax"
    );



    //RDI = iparams
    //RSI = iparams_size
    //RDX = slab entrystub; used for SYSEXIT
    //RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
    //R8 = oparams
    //R9 = oparams_size
    //R10 = src_slabid
    //R11 = cpuid


    asm volatile(
         "movq %0, %%rdi \r\n"
         "movq %1, %%rsi \r\n"
         "movq %2, %%rdx \r\n"
         "movq %3, %%rcx \r\n"
         "movq %4, %%r8 \r\n"
         "movq %5, %%r9 \r\n"
         "movq %6, %%r10 \r\n"
         "movq %7, %%r11 \r\n"

         "sysexitq \r\n"
         //"int $0x03 \r\n"
        :
        : "i" (NULL),
          "i" (0),
          "m" (entrystub),
          "m" (slabtos),
          "i" (NULL),
          "i" (0),
          "i" (0xFFFFFFFFFFFFFFFFULL),
          "m" (cpuid)


        : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
    );
*/

}


//////////////////////////////////////////////////////////////////////////////
//
// HIC trampoline



//HIC runtime trampoline stub

//__xmhfhic_rtm_trampoline stub entry register mappings:
//
//RDI = call type (XMHF_HIC_SLABCALL)
//RSI = iparams
//RDX = iparams_size
//RCX = oparams
//R8 = oparams_size
//R9 = dst_slabid
//R10 = return RSP;
//R11 = return_address


__attribute__((naked)) void __xmhfhic_rtm_trampoline_stub(void){

/*
    //TODO: x86_64 --> x86
    asm volatile (
        "cmpq %0, %%rdi \r\n"
        "je 1f \r\n"

        "pushq %%r10 \r\n"          //push return RSP
        "pushq %%r11 \r\n"          //push return address

       	"movq %1, %%rax \r\n"       //RAX=X86XMP_LAPIC_ID_MEMORYADDRESS
		"movl (%%eax), %%eax\r\n"   //EAX(bits 0-7)=LAPIC ID
        "shrl $24, %%eax\r\n"       //EAX=LAPIC ID
        "movq __xmhfhic_x86vmx_cpuidtable+0x0(,%%eax,8), %%rax\r\n" //RAX = 0-based cpu index for the CPU
        "pushq %%rax \r\n"          //push cpuid

        "movq %%cr3, %%rax \r\n"
        "andq $0x00000000000FF000, %%rax \r\n"
        "shr $12, %%rax \r\n"
        "pushq %%rax \r\n"          //push source slab id

        "callq __xmhfhic_rtm_trampoline \r\n"
        "hlt \r\n"

        "1: \r\n"
        "pushq %%r10 \r\n"          //push return RSP
        "pushq %%r11 \r\n"          //push return address

       	"movq %1, %%rax \r\n"       //RAX=X86XMP_LAPIC_ID_MEMORYADDRESS
		"movl (%%eax), %%eax\r\n"   //EAX(bits 0-7)=LAPIC ID
        "shrl $24, %%eax\r\n"       //EAX=LAPIC ID
        "movq __xmhfhic_x86vmx_cpuidtable+0x0(,%%eax,8), %%rax\r\n" //RAX = 0-based cpu index for the CPU
        "pushq %%rax \r\n"          //push cpuid

        "movq %%cr3, %%rax \r\n"
        "andq $0x00000000000FF000, %%rax \r\n"
        "shr $12, %%rax \r\n"
        "pushq %%rax \r\n"          //push source slab id

        "callq __xmhfhic_rtm_uapihandler \r\n"

        "addq $16, %%rsp \r\n"
        "popq %%rdx \r\n"
        "popq %%rcx \r\n"
        "sysexitq \r\n"

        "hlt \r\n"
      :
      : "i" (XMHF_HIC_UAPI), "i" (X86SMP_LAPIC_ID_MEMORYADDRESS)
      :
    );

    */
}








void __xmhfhic_trampoline_slabxfer_h2h(u64 iparams, u64 iparams_size,
                                       u64 entrystub, u64 slabtos,
                                       u64 oparams, u64 oparams_size,
                                       u64 src_slabid, u64 cpuid){

/*
                    //TODO: x86_64 --> x86

                    //RDI = newiparams
                    //RSI = iparams_size
                    //RDX = slab entrystub; used for SYSEXIT
                    //RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
                    //R8 = newoparams
                    //R9 = oparams_size
                    //R10 = src_slabid
                    //R11 = cpuid


                    asm volatile(
                         "movq %0, %%rdi \r\n"
                         "movq %1, %%rsi \r\n"
                         "movq %2, %%rdx \r\n"
                         "movq %3, %%rcx \r\n"
                         "movq %4, %%r8 \r\n"
                         "movq %5, %%r9 \r\n"
                         "movq %6, %%r10 \r\n"
                         "movq %7, %%r11 \r\n"

                         "sysexitq \r\n"
                         //"int $0x03 \r\n"
                         //"1: jmp 1b \r\n"
                        :
                        : "m" (iparams),
                          "m" (iparams_size),
                          "m" (entrystub),
                          "m" (slabtos),
                          "m" (oparams),
                          "m" (oparams_size),
                          "m" (src_slabid),
                          "m" (cpuid)
                        : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
                    );
*/



}



void __xmhfhic_trampoline_slabxfer_h2g(void){
/*                    u32 errorcode;

                    asm volatile (
                            "vmlaunch\r\n"

                            "jc __vmx_start_hvm_failinvalid\r\n"
                            "jnz	__vmx_start_hvm_undefinedimplementation	\r\n"
                            "movl $0x1, %%eax\r\n"		//VMLAUNCH error, XXX: need to read from VM instruction error field in VMCS
                            "movl %%eax, %0 \r\n"
                            "jmp __vmx_start_continue \r\n"
                            "__vmx_start_hvm_undefinedimplementation:\r\n"
                            "movl $0x2, %%eax\r\n"		//violation of VMLAUNCH specs., handle it anyways
                            "movl %%eax, %0 \r\n"
                            "jmp __vmx_start_continue \r\n"
                            "__vmx_start_hvm_failinvalid:\r\n"
                            "xorl %%eax, %%eax\r\n"		//return 0 as we have no error code available
                            "movl %%eax, %0 \r\n"
                            "__vmx_start_continue:\r\n"
                        : "=g"(errorcode)
                        :
                        : "eax", "cc"
                    );


                    switch(errorcode){
                        case 0:	//no error code, VMCS pointer is invalid
                            _XDPRINTF_("%s: VMLAUNCH error; VMCS pointer invalid?\n", __FUNCTION__);
                            break;
                        case 1:{//error code available, so dump it
                            u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
                            _XDPRINTF_("\n%s: VMLAUNCH error; code=%x\n", __FUNCTION__, code);
                            break;
                        }
                    }

                    HALT();

*/
}





void __xmhfhic_trampoline_slabxfer_callexception(u64 iparams, u64 iparams_size,
                                                 u64 entrystub, u64 slabtos,
                                                 u64 src_slabid, u64 cpuid){


/*
                //TODO: x86_64 --> x86

                //RDI = newiparams
                //RSI = iparams_size
                //RDX = slab entrystub; used for SYSEXIT
                //RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
                //R8 = 0 (oparams)
                //R9 = 0 (oparams_size)
                //R10 = src_slabid
                //R11 = cpuid



                asm volatile(
                     "movq %0, %%rdi \r\n"
                     "movq %1, %%rsi \r\n"
                     "movq %2, %%rdx \r\n"
                     "movq %3, %%rcx \r\n"
                     "movq %4, %%r8 \r\n"
                     "movq %5, %%r9 \r\n"
                     "movq %6, %%r10 \r\n"
                     "movq %7, %%r11 \r\n"

                     "sysexitq \r\n"
                     //"int $0x03 \r\n"
                     //"1: jmp 1b \r\n"
                    :
                    : "m" (iparams),
                      "m" (iparams_size),
                      "m" (entrystub),
                      "m" (slabtos),
                      "i" (0),
                      "i" (0),
                      "m" (src_slabid),
                      "m" (cpuid)
                    : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
                );
*/


}




void __xmhfhic_trampoline_slabxfer_callintercept(u64 entrystub, u64 slabtos,
                                                 u64 src_slabid, u64 cpuid){

/*
            //TODO: x86_64 --> x86

            //RDI = newiparams (NULL)
            //RSI = iparams_size (0)
            //RDX = slab entrystub; used for SYSEXIT
            //RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
            //R8 = newoparams (NULL)
            //R9 = oparams_size (0)
            //R10 = src_slabid
            //R11 = cpuid



            asm volatile(
                 "movq %0, %%rdi \r\n"
                 "movq %1, %%rsi \r\n"
                 "movq %2, %%rdx \r\n"
                 "movq %3, %%rcx \r\n"
                 "movq %4, %%r8 \r\n"
                 "movq %5, %%r9 \r\n"
                 "movq %6, %%r10 \r\n"
                 "movq %7, %%r11 \r\n"
                 "sysexitq \r\n"
                 //"int $0x03 \r\n"
                 //"1: jmp 1b \r\n"
                :
                : "i" (0),
                  "i" (0),
                  "m" (entrystub),
                  "m" (slabtos),
                  "i" (0),
                  "i" (0),
                  "m" (src_slabid),
                  "m" (cpuid)
                : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
            );
*/

}


void __xmhfhic_trampoline_slabxfer_retintercept(u64 addrgprs){

/*
            //TODO: x86_64 --> x86
            asm volatile (
                "movq %0, %%rsp \r\n"
                "popq %%r8 \r\n"
                "popq %%r9 \r\n"
                "popq %%r10 \r\n"
                "popq %%r11 \r\n"
                "popq %%r12 \r\n"
                "popq %%r13 \r\n"
                "popq %%r14 \r\n"
                "popq %%r15 \r\n"
                "popq %%rax \r\n"
                "popq %%rbx \r\n"
                "popq %%rcx \r\n"
                "popq %%rdx \r\n"
                "popq %%rsi \r\n"
                "popq %%rdi \r\n"
                "popq %%rbp \r\n"

                "vmresume \r\n"
                :
                : "g" (addrgprs)
                : "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
                  "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp"

            );
*/


}



void __xmhfhic_trampoline_slabxfer_retexception(u64 addr_exframe){

/*
                    //TODO: x86_64 --> x86
                    asm volatile (
                        "movq %0, %%rsp \r\n"
                        "popq %%r8 \r\n"
                        "popq %%r9 \r\n"
                        "popq %%r10 \r\n"
                        "popq %%r11 \r\n"
                        "popq %%r12 \r\n"
                        "popq %%r13 \r\n"
                        "popq %%r14 \r\n"
                        "popq %%r15 \r\n"
                        "popq %%rax \r\n"
                        "popq %%rbx \r\n"
                        "popq %%rcx \r\n"
                        "popq %%rdx \r\n"
                        "popq %%rsi \r\n"
                        "popq %%rdi \r\n"
                        "popq %%rbp \r\n"
                        "popq %%rsp \r\n"
                        "addq $16, %%rsp \r\n"
                        "iretq \r\n"
                        :
                        : "m" (addr_exframe)
                        : "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
                          "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"

                    );
*/

}
