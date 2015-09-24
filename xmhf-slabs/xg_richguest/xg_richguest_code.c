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
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xg_richguest.h>

//////
//XMHF_SLAB_GUEST(xcguestslab)



/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


// only used for guest slabs
__attribute__ ((section(".rwdatahdr"))) guest_slab_header_t _guestslabheader =
    {
        {0},
        {0},
        {0},
        GUEST_SLAB_HEADER_MAGIC,
        {0},
        {0},
    };



static void xcguestslab_dotest_vmcall(void){

    {
        u64 tscbefore, tscafter, tscavg=0;
        u32 iterations=8192;
        u32 i;

        _XDPRINTF_("%s: proceeding with test...\n", __func__);



        for(i=0; i < iterations; i++){
            tscbefore = CASM_FUNCCALL(rdtsc64,CASM_NOPARAM);

            {

                //asm volatile ("vmcall \r\n");

            }

            tscafter = CASM_FUNCCALL(rdtsc64,CASM_NOPARAM);
            tscavg += (tscafter - tscbefore);
        }

        tscavg = tscavg / iterations;

        _XDPRINTF_("%s: clock cycles for test = %u\n", __func__, (u32)tscavg);

    }



}

static void xcguestslab_do_vmcall(void){
    u32 magic = 0xAABBCCDDUL;

    _XDPRINTF_("%s: Going for VMCALL, magic=%08x\n",
                __func__, magic);

    magic =  _xcguestslab_vmcall(magic, 0, 0);

    _XDPRINTF_("%s: Came back from VMCALL, magic=%08x\n",
                __func__, magic);


}


static void xcguestslab_do_xmhfhw_cpu_cpuid(void){
    u32 dummy;
    u32 vendor_dword1, vendor_dword2, vendor_dword3;


    _XDPRINTF_("%s: Preparing to execute CPUID...\n",
                __func__);

 CASM_FUNCCALL(xmhfhw_cpu_cpuid,0, &dummy, &vendor_dword1, &vendor_dword3, &vendor_dword2);

    _XDPRINTF_("%s: CPUID(0) %x, %x, %x\n",
                __func__, vendor_dword1, vendor_dword2, vendor_dword3);
}


static void xcguestslab_do_msrtest(void){
    u64 sysenter_cs_msr;


	CASM_FUNCCALL(wrmsr64,IA32_SYSENTER_CS_MSR, 0xAA, 0);

    _XDPRINTF_("%s: wrote SYSENTER_CS_MSR.\n", __func__);

    sysenter_cs_msr = CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_CS_MSR);

    _XDPRINTF_("%s: read SYSENTER_CS_MSR=%016llx...\n", __func__, sysenter_cs_msr);

}


//////
// hyperdep test harness

//////////////////////////////////////////////////////////////////////////////
// xhhyperdep test

__attribute__((aligned(4096))) static u8 _xcguestslab_do_testxhhyperdep_page[4096];

#define HYPERDEP_ACTIVATEDEP			0xC0
#define HYPERDEP_DEACTIVATEDEP			0xC1

typedef void (*DEPFN)(void);

void xcguestslab_do_testxhhyperdep(void){
    u32 gpa = &_xcguestslab_do_testxhhyperdep_page;
    DEPFN fn = (DEPFN)gpa;

    _xcguestslab_do_testxhhyperdep_page[0] = 0xC3; //ret instruction

    _XDPRINTF_("%s: Going to activate DEP on page %x\n", __func__, gpa);


    _xcguestslab_vmcall(HYPERDEP_ACTIVATEDEP,  0, gpa);

    _XDPRINTF_("%s: Activated DEP\n", __func__);

    //fn();

    _XDPRINTF_("%s: Going to de-activate DEP on page %x\n", __func__, gpa);

    _xcguestslab_vmcall(HYPERDEP_DEACTIVATEDEP,  0, gpa);

    _XDPRINTF_("%s: Deactivated DEP\n", __func__);

}




//////
// approvexec test harness
extern void _xcguestslab_do_testxhapprovexec_functoprotect(void);



#define APPROVEXEC_LOCK     			0xD0
#define APPROVEXEC_UNLOCK   			0xD1

void xcguestslab_do_testxhapprovexec(void){
    u32 gpa = &_xcguestslab_do_testxhapprovexec_functoprotect;

    _XDPRINTF_("%s: Going to approve and lock function at %x\n", __func__, gpa);

    _xcguestslab_vmcall(APPROVEXEC_LOCK, 0, gpa);

    _XDPRINTF_("%s: Locked function\n", __func__);

    /*{
        u8 *pokefun = (u8 *)&_xcguestslab_do_testxhapprovexec_functoprotect;
        pokefun[0] = 0xAB;
    }*/

    _XDPRINTF_("%s: Going to unlock function on page %x\n", __func__, gpa);

    _xcguestslab_vmcall(APPROVEXEC_UNLOCK, 0, gpa );

    _XDPRINTF_("%s: unlocked function\n", __func__);

}







//////
// ssteptrace test harness

//////////////////////////////////////////////////////////////////////////////
// xhssteptrace test

#define SSTEPTRACE_REGISTER    			0xE0
#define SSTEPTRACE_ON          			0xE1
#define SSTEPTRACE_OFF         			0xE2

__attribute__((aligned(4096))) void _xcguestslab_do_testxhssteptrace_func(void){

    _XDPRINTF_("%s: Turning on tracing...\n", __func__);

    _xcguestslab_vmcall(SSTEPTRACE_ON, 0, 0);

    /*asm volatile(
        "nop \r\n"
        "nop \r\n"
        "nop \r\n"
        :
        :
        :
    );*/

    _xcguestslab_vmcall(SSTEPTRACE_OFF, 0 , 0);

    _XDPRINTF_("%s: Tracing off...\n", __func__);

}


static void xcguestslab_do_testxhssteptrace(void){
    /*u64 gpa = &_xcguestslab_do_testxhssteptrace_func;

    _XDPRINTF_("%s: Going to register function at %016llx\n", __func__, gpa);

    asm volatile(
        "movl %0, %%eax \r\n"
        "movl %1, %%edx \r\n"
        "movl %2, %%ebx \r\n"
        "vmcall \r\n"
        :
        : "i" (SSTEPTRACE_REGISTER),
          "g" ( (u32) ((u64)(gpa >> 32)) ),
          "g" ((u32)gpa)
        : "eax", "ebx", "edx"
    );

    _XDPRINTF_("%s: Registered function\n", __func__);
*/
    _XDPRINTF_("%s: Proceeding to call function...\n", __func__);

    _xcguestslab_do_testxhssteptrace_func();

    _XDPRINTF_("%s: Came back from calling function.\n", __func__);

}





//////
// syscalllog test harness


//*
// GDT
__attribute__(( aligned(16) )) u64 _xcguestslab_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00cf9a000000ffffULL,	//CPL-0 32-bit code descriptor (CS32)
	0x00cf92000000ffffULL,	//CPL-0 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS32)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS32)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x0000000000000000ULL,  //TSS descriptors
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
__attribute__(( aligned(16) )) arch_x86_gdtdesc_t _xcguestslab_gdt  = {
	.size=sizeof(_xcguestslab_gdt_start)-1,
	.base=(u32)&_xcguestslab_gdt_start,
};


/////////
#define SYSCALLLOG_REGISTER     			0xF0

static u8 _xcguestslab_do_testxhsyscalllog_sysenterhandler_stack[PAGE_SIZE_4K];



extern void _xcguestslab_do_testxhsyscalllog_sysenterhandler(void);

void xcguestslab_do_testxhsyscalllog(void){
    u32 gpa = &_xcguestslab_do_testxhsyscalllog_sysenterhandler;

    _XDPRINTF_("%s: proceeding to load GDT\n", __func__);

    _xcguestslab_do_testxhsyscalllog_loadGDT( (u32)&_xcguestslab_gdt, __CS_CPL0, __DS_CPL0 );

    _XDPRINTF_("%s: GDT loaded\n", __func__);

    _xcguestslab_do_testxhsyscalllog_setIOPL3();

    _xcguestslab_vmcall(SYSCALLLOG_REGISTER, 0, gpa);

    _XDPRINTF_("%s: registered syscall handler on page %x\n", __func__, gpa);

    //setup SYSENTER/SYSEXIT mechanism
    {
 CASM_FUNCCALL(wrmsr64,IA32_SYSENTER_CS_MSR, __CS_CPL0, 0);
 CASM_FUNCCALL(wrmsr64,IA32_SYSENTER_EIP_MSR, &_xcguestslab_do_testxhsyscalllog_sysenterhandler, 0);
 CASM_FUNCCALL(wrmsr64,IA32_SYSENTER_ESP_MSR, ((u32)&_xcguestslab_do_testxhsyscalllog_sysenterhandler_stack + (u32)PAGE_SIZE_4K), 0);
    }
    _XDPRINTF_("%s: setup SYSENTER/SYSEXIT mechanism\n", __func__);
    _XDPRINTF_("%s: SYSENTER CS=%016llx\n", __func__, CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_CS_MSR));
    _XDPRINTF_("%s: SYSENTER RIP=%016llx\n", __func__, CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_EIP_MSR));
    _XDPRINTF_("%s: SYSENTER RSP=%016llx\n", __func__, CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_ESP_MSR));


    _xcguestslab_do_testxhsyscalllog_switchtoring3();

    _XDPRINTF_("%s: Guest Slab at Ring-3. Proceeding to execute sysenter...Halting!\n", __func__);

    _xcguestslab_do_testxhsyscalllog_invokesyscall();

    _XDPRINTF_("%s: Came back from SYSENTER\n", __func__);

    _XDPRINTF_("%s: Guest Slab Halting\n", __func__);
    HALT();
}







void slab_main(slab_params_t *sp){
    _XDPRINTF_("%s: Hello world from Guest slab! ESP=%08x, flags=%08x\n", __func__, read_esp(CASM_NOPARAM),
		read_eflags(CASM_NOPARAM));

    //xcguestslab_do_vmcall();

    //xcguestslab_do_xmhfhw_cpu_cpuid();

    //xcguestslab_do_msrtest();

    xcguestslab_do_testxhhyperdep();

    xcguestslab_do_testxhapprovexec();

    xcguestslab_do_testxhssteptrace();

    xcguestslab_do_testxhsyscalllog();

    _XDPRINTF_("%s: Guest Slab Halting\n", __func__);
    HALT();
}
