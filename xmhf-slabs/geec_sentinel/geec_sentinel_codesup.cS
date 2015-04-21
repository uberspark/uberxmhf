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
 GEEC sentinel low-level support routines
 author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>
#include <geec_sentinel.h>


//////
// sentinel entry point
//////

CASM_FUNCDEF(void, slab_main,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_pushl_ebp();
    xmhfhwm_cpu_insn_pushl_edi();
    xmhfhwm_cpu_insn_pushl_esi();
    xmhfhwm_cpu_insn_pushl_ebx();
    xmhfhwm_cpu_insn_movl_esp_edx();
    xmhfhwm_cpu_insn_pushl_edx();
    xmhfhwm_cpu_insn_pushl_eax();
    xmhfhwm_cpu_insn_call(geec_sentinel_main);
    xmhfhwm_cpu_insn_hlt();
},
slab_params_t *sp)





//////
// CASM sentinel stubs -- the following get called by the hardware
//////



////// exceptions

#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	CASM_FUNCDEF(void, __xmhf_exception_handler_##vector, 					\
    { \
        xmhfhwm_cpu_insn_pushl_imm(vector); \
        xmhfhwm_cpu_insn_pushal(); \
        xmhfhwm_cpu_insn_pushl_esp(); \
        xmhfhwm_cpu_insn_call(_geec_sentinel_exception_stub); \
        xmhfhwm_cpu_insn_hlt(); \
    },\
    void *noparam) \

#define XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(vector) 												\
	CASM_FUNCDEF(void, __xmhf_exception_handler_##vector, 					\
    {\
		xmhfhwm_cpu_insn_pushl_imm(0x0); \
        xmhfhwm_cpu_insn_pushl_imm(vector); \
        xmhfhwm_cpu_insn_pushal(); \
        xmhfhwm_cpu_insn_pushl_esp(); \
        xmhfhwm_cpu_insn_call(_geec_sentinel_exception_stub); \
        xmhfhwm_cpu_insn_hlt(); \
    },\
    void *noparam) \



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







////// intercepts

CASM_FUNCDEF(void, _geec_sentinel_intercept_casmstub,
{
    xmhfhwm_cpu_insn_pushal();
    xmhfhwm_cpu_insn_pushl_esp();
    xmhfhwm_cpu_insn_call(_geec_sentinel_intercept_stub);
    //xmhfhwm_cpu_insn_addl_imm_esp(0x4);
    //xmhfhwm_cpu_insn_popal();
    //xmhfhwm_cpu_insn_vmresume();
    xmhfhwm_cpu_insn_hlt();
},
void *noparam)





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


//__attribute__((naked)) void __xmhfhic_rtm_trampoline_stub(void){
CASM_FUNCDEF(void, __xmhfhic_rtm_trampoline_stub,
{

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
},
void *noparam)






















//////
// support CASM functions used by the sentinel
/////


CASM_FUNCDEF(void, _geec_sentinel_xfer_vft_prog_to_vft_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    xmhfhwm_cpu_insn_movl_edx_esp();
    xmhfhwm_cpu_insn_popl_ebx();
    xmhfhwm_cpu_insn_popl_esi();
    xmhfhwm_cpu_insn_popl_edi();
    xmhfhwm_cpu_insn_popl_ebp();
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();
},
u32 entry_point, void *caller_stack_frame)



CASM_FUNCDEF(void, _geec_sentinel_xfer_exception_to_vft_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    xmhfhwm_cpu_insn_movl_edx_esp();
    xmhfhwm_cpu_insn_pushl_esp();
    xmhfhwm_cpu_insn_pushl_imm(0x0);
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();
},
u32 entry_point, void *caller_stack_frame)

CASM_FUNCDEF(void, _geec_sentinel_xfer_ret_from_exception,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);    //eax = exception frame
    xmhfhwm_cpu_insn_movl_meax_edi(0x0);
    xmhfhwm_cpu_insn_movl_meax_esi(0x4);
    xmhfhwm_cpu_insn_movl_meax_ebp(0x8);
    xmhfhwm_cpu_insn_movl_meax_esp(0xC);
    xmhfhwm_cpu_insn_movl_meax_ebx(0x10);
    xmhfhwm_cpu_insn_movl_meax_edx(0x14);
    xmhfhwm_cpu_insn_movl_meax_ecx(0x18);
    xmhfhwm_cpu_insn_movl_meax_eax(0x1C);
    xmhfhwm_cpu_insn_addl_imm_esp(0x8);
    xmhfhwm_cpu_insn_iretl();
},
x86vmx_exception_frame_t *exframe)


CASM_FUNCDEF(void, _geec_sentinel_xfer_intercept_to_vft_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    xmhfhwm_cpu_insn_movl_edx_esp();
    xmhfhwm_cpu_insn_pushl_esp();
    xmhfhwm_cpu_insn_pushl_imm(0x0);
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();
},
u32 entry_point, void *caller_stack_frame)


//if we return, we had an error and we return the
//corresponding error code
CASM_FUNCDEF(u32, _geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog_guest,
{
    xmhfhwm_cpu_insn_vmlaunch();
    xmhfhwm_cpu_insn_jc(__vmx_start_hvm_failinvalid);
    xmhfhwm_cpu_insn_jnz(__vmx_start_hvm_undefinedimplementation);
    xmhfhwm_cpu_insn_movl_imm_eax(0x1);		//VMLAUNCH error, XXX: need to read from VM instruction error field in VMCS
    xmhfhwm_cpu_insn_jmp(__vmx_start_continue);
    CASM_LABEL(__vmx_start_hvm_undefinedimplementation);
    xmhfhwm_cpu_insn_movl_imm_eax(0x2);		//violation of VMLAUNCH specs., handle it anyways
    xmhfhwm_cpu_insn_jmp(__vmx_start_continue);
    CASM_LABEL(__vmx_start_hvm_failinvalid);
    xmhfhwm_cpu_insn_xorl_eax_eax();		//return 0 as we have no error code available
    CASM_LABEL(__vmx_start_continue);
    xmhfhwm_cpu_insn_ret();
},
void *noparam)




CASM_FUNCDEF(void, _geec_sentinel_xfer_ret_from_intercept,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_meax_edi(0x0);
    xmhfhwm_cpu_insn_movl_meax_esi(0x4);
    xmhfhwm_cpu_insn_movl_meax_ebp(0x8);
    xmhfhwm_cpu_insn_movl_meax_esp(0xC);
    xmhfhwm_cpu_insn_movl_meax_ebx(0x10);
    xmhfhwm_cpu_insn_movl_meax_edx(0x14);
    xmhfhwm_cpu_insn_movl_meax_ecx(0x18);
    xmhfhwm_cpu_insn_movl_meax_eax(0x1C);
    xmhfhwm_cpu_insn_vmresume();
    xmhfhwm_cpu_insn_hlt();
},
x86regs_t *r)



CASM_FUNCDEF(void, _geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog,
{
    //xmhfhwm_cpu_insn_movl_mesp_edx(0x4);    //edx = entry_point
    //xmhfhwm_cpu_insn_movl_mesp_ecx(0x8);    //edx = callee_stack_frame
    //xmhfhwm_cpu_insn_sysexit();             //sysexit to ring-3
    //xmhfhwm_cpu_insn_hlt();

    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    xmhfhwm_cpu_insn_movl_edx_esp();
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();

},
u32 entry_point, void *callee_stack_frame)
