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
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcprimeon.h>


//ring3 stack and tos
__attribute__(( aligned(4096) )) static u8 _exp_ring3stack[PAGE_SIZE_4K] = { 0 };
static u64 _exp_ring3tos = (u64)&_exp_ring3stack + (u64)PAGE_SIZE_4K;


// GDT
__attribute__(( aligned(16) )) static u64 _exp_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00af9a000000ffffULL,	//CPL-0 64-bit code descriptor (CS64)
	0x00af92000000ffffULL,	//CPL-0 64-bit data descriptor (DS/SS/ES/FS/GS)
	0x00affa000000ffffULL,	//TODO: CPL-3 64-bit code descriptor (CS64)
	0x00aff2000000ffffULL,	//TODO: CPL-3 64-bit data descriptor (DS/SS/ES/FS/GS)
	0x0000000000000000ULL,  //TSS descriptor
	0x0000000000000000ULL,
};

// GDT descriptor
__attribute__(( aligned(16) )) static arch_x86_gdtdesc_t _exp_gdt  = {
	.size=sizeof(_exp_gdt_start)-1,
	.base=(u64)&_exp_gdt_start,
};


// TSS
__attribute__(( aligned(4096) )) static u8 _exp_tss[PAGE_SIZE_4K] = { 0 };

__attribute__(( aligned(4096) )) static u8 _exp_tss_stack[PAGE_SIZE_4K];


// IDT
__attribute__(( aligned(16) )) static idtentry_t _exp_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS] ;

// IDT descriptor
__attribute__(( aligned(16) )) static arch_x86_idtdesc_t _exp_idt = {
	.size=sizeof(_exp_idt_start)-1,
	.base=(u64)&_exp_idt_start,
};


static u64 _exp_saved_rsp=0;
static u64 _exp_saved_rax=0;

__attribute__(( aligned(4096) )) static u8 _exp_idtstack[PAGE_SIZE_4K] = { 0 };
static u64 _exp_idttos = (u64)&_exp_idtstack + (u64)PAGE_SIZE_4K;


#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	static void __exp_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
                        "movq %%rax, %0 \r\n"\
                        "movq %%rsp, %1 \r\n"\
                        "movq %2, %%rax \r\n"\
                        "movw %%ax, %%ss \r\n"\
                        "movq %3, %%rsp \r\n"				    \
                        "movq %0, %%rax \r\n"\
                                                                    \
                        "pushq %1 \r\n"\
                        "pushq %%rbp \r\n"\
                        "pushq %%rdi \r\n"\
                        "pushq %%rsi \r\n"\
                        "pushq %%rdx \r\n"\
                        "pushq %%rcx \r\n"\
                        "pushq %%rbx \r\n"\
                        "pushq %%rax \r\n"\
                        "pushq %%r15 \r\n"\
                        "pushq %%r14 \r\n"\
                        "pushq %%r13 \r\n"\
                        "pushq %%r12 \r\n"\
                        "pushq %%r11 \r\n"\
                        "pushq %%r10 \r\n"\
                        "pushq %%r9 \r\n"\
                        "pushq %%r8 \r\n"\
                        "movq %%rsp, %%rsi \r\n"\
                        "mov %4, %%rdi \r\n"\
                        "callq xmhf_xcphandler_arch_hub \r\n"\
                        "cmpq $0, %%rax \r\n"\
                        "jne 3f\r\n"\
                        "hlt\r\n"\
                        "3:\r\n"\
                        "popq %%r8 \r\n"\
                        "popq %%r9 \r\n"\
                        "popq %%r10 \r\n"\
                        "popq %%r11 \r\n"\
                        "popq %%r12 \r\n"\
                        "popq %%r13 \r\n"\
                        "popq %%r14 \r\n"\
                        "popq %%r15 \r\n"\
                        "popq %%rax \r\n"\
                        "popq %%rbx \r\n"\
                        "popq %%rcx \r\n"\
                        "popq %%rdx \r\n"\
                        "popq %%rsi \r\n"\
                        "popq %%rdi \r\n"\
                        "popq %%rbp \r\n"\
                        "popq %%rsp \r\n"\
                        \
                        "iretq \r\n"\
					:												\
					:	"m" (_exp_saved_rax), "m" (_exp_saved_rsp), "i"(__DS_CPL0), "m" (_exp_idttos), "i" (vector)				\
		);															\
	}\


#define XMHF_EXCEPTION_HANDLER_ADDROF(vector) &__exp_exception_handler_##vector

XMHF_EXCEPTION_HANDLER_DEFINE(0)
XMHF_EXCEPTION_HANDLER_DEFINE(1)
XMHF_EXCEPTION_HANDLER_DEFINE(2)
XMHF_EXCEPTION_HANDLER_DEFINE(3)
XMHF_EXCEPTION_HANDLER_DEFINE(4)
XMHF_EXCEPTION_HANDLER_DEFINE(5)
XMHF_EXCEPTION_HANDLER_DEFINE(6)
XMHF_EXCEPTION_HANDLER_DEFINE(7)
XMHF_EXCEPTION_HANDLER_DEFINE(8)
XMHF_EXCEPTION_HANDLER_DEFINE(9)
XMHF_EXCEPTION_HANDLER_DEFINE(10)
XMHF_EXCEPTION_HANDLER_DEFINE(11)
XMHF_EXCEPTION_HANDLER_DEFINE(12)
XMHF_EXCEPTION_HANDLER_DEFINE(13)
XMHF_EXCEPTION_HANDLER_DEFINE(14)
XMHF_EXCEPTION_HANDLER_DEFINE(15)
XMHF_EXCEPTION_HANDLER_DEFINE(16)
XMHF_EXCEPTION_HANDLER_DEFINE(17)
XMHF_EXCEPTION_HANDLER_DEFINE(18)
XMHF_EXCEPTION_HANDLER_DEFINE(19)
XMHF_EXCEPTION_HANDLER_DEFINE(20)
XMHF_EXCEPTION_HANDLER_DEFINE(21)
XMHF_EXCEPTION_HANDLER_DEFINE(22)
XMHF_EXCEPTION_HANDLER_DEFINE(23)
XMHF_EXCEPTION_HANDLER_DEFINE(24)
XMHF_EXCEPTION_HANDLER_DEFINE(25)
XMHF_EXCEPTION_HANDLER_DEFINE(26)
XMHF_EXCEPTION_HANDLER_DEFINE(27)
XMHF_EXCEPTION_HANDLER_DEFINE(28)
XMHF_EXCEPTION_HANDLER_DEFINE(29)
XMHF_EXCEPTION_HANDLER_DEFINE(30)
XMHF_EXCEPTION_HANDLER_DEFINE(31)

static u64 _exp_exceptionstubs[] = { 	XMHF_EXCEPTION_HANDLER_ADDROF(0),
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



__attribute__((naked)) static void __exp_syscallhandler(void){
    asm volatile(
      "sysexit \r\n"
      :
      :
      :
    );

}





//load GDT and initialize segment registers
static void _exp_loadGDT(void){

	asm volatile(
		"lgdt  %0 \r\n"
		"pushq	%1 \r\n"				// far jump to runtime entry point
		"pushq	$reloadsegs \r\n"
		"lretq \r\n"
		"reloadsegs: \r\n"
		"movw	%2, %%ax \r\n"
		"movw	%%ax, %%ds \r\n"
		"movw	%%ax, %%es \r\n"
		"movw	%%ax, %%fs \r\n"
		"movw	%%ax, %%gs \r\n"
		"movw   %%ax, %%ss \r\n"
		: //no outputs
		: "m" (_exp_gdt), "i" (__CS_CPL0), "i" (__DS_CPL0)
		: "eax"
	);
}


//load IDT
static void _exp_loadIDT(void){
	//load IDT
	asm volatile(
		"lidt  %0 \r\n"
		: //no outputs
		: "m" (_exp_idt)
		: //no clobber
	);
}

//load TR
static void _exp_loadTR(void){
	  asm volatile(
		"xorq %%rax, %%rax\r\n"
		"movw %0, %%ax\r\n"
		"ltr %%ax\r\n"				//load TR
	     :
	     : "i"(__TRSEL)
	     : "rax"
	  );
}


//set IOPl to CPl-3
static void _exp_setIOPL3(void){

	asm volatile(
        "pushfq \r\n"
        "popq %%rax \r\n"
		"orq $0x3000, %%rax \r\n"					// clear flags, but set IOPL=3 (CPL-3)
		"pushq %%rax \r\n"
		"popfq \r\n"
		: //no outputs
		: //no inputs
		: "rax", "cc"
	);


}

//initialize TSS
static void _exp_initializeTSS(void){
		tss_t *tss= (tss_t *)_exp_tss;

		tss->rsp0 = (u64) ( (u32)_exp_tss_stack + PAGE_SIZE_4K );
}

//initialize GDT
static void _exp_initializeGDT(void){
		TSSENTRY *t;
		u32 tss_base=(u32)&_exp_tss;

		//TSS descriptor
		t= (TSSENTRY *)(u32)&_exp_gdt_start[(__TRSEL/sizeof(u64))];
		t->attributes1= 0xE9;
		t->limit16_19attributes2= 0x0;
		t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
		t->limit0_15=0x67;
}


//initialize IDT
static void _exp_initializeIDT(void){
	u32 i;

	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		_exp_idt_start[i].isrLow= (u16)_exp_exceptionstubs[i];
		_exp_idt_start[i].isrHigh= (u16) ( (u32)_exp_exceptionstubs[i] >> 16 );
		_exp_idt_start[i].isrSelector = __CS_CPL0;
		_exp_idt_start[i].count=0x0;
		_exp_idt_start[i].type=0xEE;	//32-bit interrupt gate
                                //present=1, DPL=11b, system=0, type=1110b
        _exp_idt_start[i].offset3263=0;
        _exp_idt_start[i].reserved=0;
	}

}


static void _exp_dotests(void){

    //[drop tests:begin]
    //should generate a GPF
    //_exp_loadTR();
    //should go through via IDT
    //asm volatile ("int $0x03 \r\n");
    //[drop tests:end]


    {
        u64 tscbefore, tscafter, tscavg=0;
        u32 iterations=8192;
        u32 i;

        _XDPRINTF_("%s: proceeding with test...\n", __FUNCTION__);

        for(i=0; i < iterations; i++){
            tscbefore = rdtsc64();

            //
            {
                //static u32 a=0;
                //a++;
                /* //3 clock cycles
                asm volatile (" movw %%ds, %%ax \r\n"
                              " movw %%ax, %%ds \r\n"
                              :
                              :
                              : "eax");*/

                /*//far ret: 63 clock cycles
                asm volatile ("pushl %0 \r\n"
                              "pushl $1f \r\n"
                              "lret \r\n"
                              "1: \r\n"
                              :
                              : "i" (__CS_CPL3)
                              :
                              );*/

                /*//far jmp: 63 clock cycles
                asm volatile ("ljmp %0, $1f \r\n"
                              "1: \r\n"
                              :
                              : "i" (__CS_CPL3)
                              :
                              );*/

                /*//sysenter/sysexit: 69 clock cycles
                asm volatile (
                              "movl %%esp, %%ecx \r\n"
                              "movl $1f, %%edx \r\n"
                              "sysenter \r\n"
                              "1: \r\n"
                              :
                              :
                              :
                              );*/


                /*//invlpg: 183 clock cycles
                asm volatile (
                              "invlpg %0 \r\n"
                              :
                              : "m"(_exp_ring3tos)
                              :
                              );*/

            }
            //

            tscafter = rdtsc64();
            tscavg += (tscafter - tscbefore);
        }

        tscavg = tscavg / iterations;

        _XDPRINTF_("%s: clock cycles for test = %u\n", __FUNCTION__, (u32)tscavg);

    }

}

//////
//we get in here in 32-bit protected mode with (unity) paging turned on
void xcprimeon_exp_entry(void){
    _XDPRINTF_("%s: Begin Testing...\n", __FUNCTION__);

    //init GDT
    _exp_initializeGDT();
    _XDPRINTF_("%s: GDT initialized\n", __FUNCTION__);

    //init IDT
    _exp_initializeIDT();
    _XDPRINTF_("%s: IDT initialized\n", __FUNCTION__);


    //init TSS
    _exp_initializeTSS();
    _XDPRINTF_("%s: TSS initialized\n", __FUNCTION__);

    //load GDT
    _exp_loadGDT();
    _XDPRINTF_("%s: GDT loaded\n", __FUNCTION__);

    //load TR
    _exp_loadTR();
    _XDPRINTF_("%s: TR loaded\n", __FUNCTION__);


    //load IDT
    _exp_loadIDT();
    _XDPRINTF_("%s: IDT loaded\n", __FUNCTION__);


    //set IOPL3
    _exp_setIOPL3();
    _XDPRINTF_("%s: set IOPL to CPL-3\n", __FUNCTION__);


    //setup SYSENTER/SYSEXIT mechanism
    {
        wrmsr(IA32_SYSENTER_CS_MSR, __CS_CPL0, 0);
        wrmsr(IA32_SYSENTER_EIP_MSR, (u32)&__exp_syscallhandler, 0);
        wrmsr(IA32_SYSENTER_ESP_MSR, ((u32)_exp_tss_stack + PAGE_SIZE_4K), 0);
    }
    _XDPRINTF_("%s: setup SYSENTER/SYSEXIT mechanism\n", __FUNCTION__);

/*
    //switch to ring-3
    {
        asm volatile(
             "pushq %0 \r\n"
             "pushq %1 \r\n"
             "pushq %2 \r\n"
             "pushq $1f \r\n"
             "lretq \r\n"
             "1: jmp 1b\r\n"
             "movq %0, %%rax \r\n"
             "movw %%ax, %%ds \r\n"
             "movw %%ax, %%es \r\n"
            :
            : "i" (__DS_CPL3), "m" (_exp_ring3tos), "i" (__CS_CPL3)
            : "rsp", "rax"
        );
    }
*/


    //switch to ring-3
    {
        asm volatile(
            "movq %0, %%rcx \r\n"
            "movq $1f, %%rdx \r\n"
            "sysexit \r\n"
            "1: \r\n"
            "movq %1, %%rax \r\n"
            "movw %%ax, %%ds \r\n"
            "movw %%ax, %%es \r\n"
            :
            : "m" (_exp_ring3tos), "i" (__DS_CPL3)
            : "rcx", "rdx", "rax"
        );

    }


    _XDPRINTF_("%s: Now at CPL-3...\n", __FUNCTION__);
    HALT();

    asm volatile ("int $0x03 \r\n");

    _exp_dotests();


    _XDPRINTF_("%s: Halting!\n", __FUNCTION__);
    _XDPRINTF_("%s: XMHF Tester Finished!\n", __FUNCTION__);
    HALT();
}



