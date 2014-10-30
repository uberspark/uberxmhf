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
 * slab trampoline that is mapped into every slab memory view
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>


//HIC runtime trampoline stub

/*
__xmhfhic_rtm_trampoline stub entry register mappings:

RDI = call type (XMHF_HIC_SLABCALL)
RSI = iparams
RDX = iparams_size
RCX = oparams
R8 = oparams_size
R9 = dst_slabid
R10 = return RSP;
R11 = return_address

*/

__attribute__((naked)) void __xmhfhic_rtm_trampoline_stub(void){

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
}













//HIC runtime exception stub

/*entry into __xmhfhic_rtm_trampoline:
RDI = hic_calltype
RSI = iparams
RDX = iparams_size
RCX = oparams
R8 = oparams_size
R9 = dst_slabid
[RSP] = src_slabid
[RSP+8] = cpuid
[RSP+16] = return_address
[RSP+32] = return_rsp
*/


__attribute__((naked)) void __xmhfhic_rtm_exception_stub(void){

	asm volatile(
                        "pushq %%rsp \r\n"
                        "pushq %%rbp \r\n"
                        "pushq %%rdi \r\n"
                        "pushq %%rsi \r\n"
                        "pushq %%rdx \r\n"
                        "pushq %%rcx \r\n"
                        "pushq %%rbx \r\n"
                        "pushq %%rax \r\n"
                        "pushq %%r15 \r\n"
                        "pushq %%r14 \r\n"
                        "pushq %%r13 \r\n"
                        "pushq %%r12 \r\n"
                        "pushq %%r11 \r\n"
                        "pushq %%r10 \r\n"
                        "pushq %%r9 \r\n"
                        "pushq %%r8 \r\n"

                        //rdi = hic_calltype = XMHF_HIC_SLABCALLEXCEPTION
                        "movq %0, %%rdi \r\n"

                        //iparams
                        "movq %%rsp, %%rsi \r\n"

                        //iparams_size
                        "movq %1, %%rdx \r\n"

                        //oparams
                        "movq %%rsi, %%rcx \r\n"

                        //oparams_size
                        "movq %%rdx, %%r8 \r\n"

                        //dst_slabid
                        "movq %2, %%r9 \r\n"

                        "movq %%rsp, %%rbx \r\n"

                        //return_rsp
                        "movq 168(%%rbx), %%rax \r\n"
                        "pushq %%rax \r\n"

                        //return_address
                        "movq 144(%%rbx), %%rax \r\n"
                        "pushq %%rax \r\n"

                        //cpuid
                        "movq %3, %%rax \r\n"       //RAX=X86XMP_LAPIC_ID_MEMORYADDRESS
                        "movl (%%eax), %%eax\r\n"   //EAX(bits 0-7)=LAPIC ID
                        "shrl $24, %%eax\r\n"       //EAX=LAPIC ID
                        "movq __xmhfhic_x86vmx_cpuidtable+0x0(,%%eax,8), %%rax\r\n" //RAX = 0-based cpu index for the CPU
                        "pushq %%rax \r\n"

                        //src_slabid
                        "movq %%cr3, %%rax \r\n"
                        "andq $0x00000000000FF000, %%rax \r\n"
                        "shr $12, %%rax \r\n"
                        "pushq %%rax \r\n"


                        "callq __xmhfhic_rtm_trampoline \r\n"
					:
					:   "i" (XMHF_HIC_SLABCALLEXCEPTION),
                        "i" (sizeof(x86vmx_exception_frame_errcode_t)),
                        "i" (XMHF_HYP_SLAB_XCEXHUB),
					    "i" (X86SMP_LAPIC_ID_MEMORYADDRESS)
                    :
		);
}


#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
                        "pushq %0 \r\n"\
                        "jmp __xmhfhic_rtm_exception_stub\r\n"\
					: \
					: "i" (vector) \
                    : \
               		);	\
    }\

#define XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(vector) 												\
	static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
                        "pushq $0x0 \r\n" \
                        "pushq %0 \r\n"\
                        "jmp __xmhfhic_rtm_exception_stub\r\n"\
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

u64  __xmhfhic_exceptionstubs[] = { XMHF_EXCEPTION_HANDLER_ADDROF(0),
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
__attribute__((naked)) void __xmhfhic_rtm_intercept_stub(void){

	asm volatile(
                        "pushq %%rsp \r\n"
                        "pushq %%rbp \r\n"
                        "pushq %%rdi \r\n"
                        "pushq %%rsi \r\n"
                        "pushq %%rdx \r\n"
                        "pushq %%rcx \r\n"
                        "pushq %%rbx \r\n"
                        "pushq %%rax \r\n"
                        "pushq %%r15 \r\n"
                        "pushq %%r14 \r\n"
                        "pushq %%r13 \r\n"
                        "pushq %%r12 \r\n"
                        "pushq %%r11 \r\n"
                        "pushq %%r10 \r\n"
                        "pushq %%r9 \r\n"
                        "pushq %%r8 \r\n"

                        "pushfq \r\n"
                        "popq %%rax \r\n"
                        "orq $0x3000, %%rax \r\n"
                        "pushq %%rax \r\n"
                        "popfq \r\n"

                        //rdi = hic_calltype = XMHF_HIC_SLABCALLINTERCEPT
                        "movq %0, %%rdi \r\n"

                        //iparams
                        "movq %%rsp, %%rsi \r\n"

                        //iparams_size
                        "movq %1, %%rdx \r\n"

                        //oparams
                        "movq %%rsi, %%rcx \r\n"

                        //oparams_size
                        "movq %%rdx, %%r8 \r\n"

                        //dst_slabid
                        "movq %2, %%r9 \r\n"

                        //return_rsp (NA -- since its stored in VMCS)
                        "pushq $0x0 \r\n"

                        //return_address (NA -- since its stored in VMCS)
                        "pushq $0x0 \r\n"

                        //cpuid
                        "movq %3, %%rax \r\n"       //RAX=X86XMP_LAPIC_ID_MEMORYADDRESS
                        "movl (%%eax), %%eax\r\n"   //EAX(bits 0-7)=LAPIC ID
                        "shrl $24, %%eax\r\n"       //EAX=LAPIC ID
                        "movq __xmhfhic_x86vmx_cpuidtable+0x0(,%%eax,8), %%rax\r\n" //RAX = 0-based cpu index for the CPU
                        "pushq %%rax \r\n"

                        //src_slabid
                        "movq %4, %%rax \r\n"
                        "vmread %%rax, %%rax \r\n"     //RAX = VPID = slab_id
                        "decq %%rax \r\n"
                        "pushq %%rax \r\n"


                        "callq __xmhfhic_rtm_trampoline \r\n"
					:
					:   "i" (XMHF_HIC_SLABCALLINTERCEPT),
                        "i" (sizeof(x86regs64_t)),
                        "i" (XMHF_HYP_SLAB_XCIHUB),
					    "i" (X86SMP_LAPIC_ID_MEMORYADDRESS),
                        "i" (VMCS_CONTROL_VPID)
                    :
		);
}
























//HIC runtime trampoline
void __xmhfhic_rtm_trampoline(u64 hic_calltype, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid, u64 src_slabid, u64 cpuid, u64 return_address, u64 return_rsp) {
    u8 __paramsbuffer[1024];


    //_XDPRINTF_("%s[%u]: Trampoline got control: RSP=%016llx\n",
    //                __FUNCTION__, (u32)cpuid, read_rsp());

    //_XDPRINTF_("%s[%u]: Trampoline got control: hic_calltype=%x, iparams=%x, iparams_size=%u, \
    //           oparams=%x, oparams_size=%u, dst_slabid=%x, src_slabid=%x, cpuid=%x, return_address=%016llx \
    //           return_rsp=%x\n",
    //                __FUNCTION__, (u32)cpuid,
    //           hic_calltype, iparams, iparams_size, oparams, oparams_size,
    //           dst_slabid, src_slabid, cpuid, return_address, return_rsp);

    switch(hic_calltype){

        case XMHF_HIC_SLABCALL:{
            //check to see if source slab can invoke destination slab
            if(!__xmhfhic_callcaps(src_slabid, dst_slabid)){
                _XDPRINTF_("%s[%u]: Fatal: Slab %u does not have capabilities to invoke Slab %u. Halting!\n",
                    __FUNCTION__, (u32)cpuid, src_slabid, dst_slabid);
                HALT();
            }


            switch(_xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtype){

                case HIC_SLAB_X86VMXX86PC_HYPERVISOR:{
                    slab_input_params_t *newiparams;
                    slab_output_params_t *newoparams;

                    //save return RSP
                    _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtos[(u32)cpuid] = return_rsp;

                    //copy iparams to internal buffer __paramsbuffer
                    memcpy(&__paramsbuffer, iparams, (iparams_size > 1024 ? 1024 : iparams_size) );

                    //switch to destination slab page tables
                    asm volatile(
                         "movq %0, %%rax \r\n"
                         "movq %%rax, %%cr3 \r\n"
                        :
                        : "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3)
                        : "rax"
                    );

                    //make space on destination slab stack for iparams and copy iparams and obtain newiparams
                    {
                        _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid] -= iparams_size;
                        newiparams = (slab_input_params_t *) _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid];
                        memcpy((void *)_xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid],
                               &__paramsbuffer, (iparams_size > 1024 ? 1024 : iparams_size) );
                    }


                    //make space on destination slab stack for oparams and obtain newoparams
                    {
                        _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid] -= oparams_size;
                        newoparams = (slab_output_params_t *) _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid];
                    }


                    //push cpuid, src_slabid, dst_slabid, hic_calltype, return_address, oparams, new oparams and oparams_size tuple to
                    //safe stack
                    //_XDPRINTF_("%s[%u]: safepush: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x, ra=%016llx, \
                    //           op=%016llx, newop=%016llx, opsize=%u\n",
                    //        __FUNCTION__, (u32)cpuid,
                    //           cpuid, src_slabid, dst_slabid, hic_calltype, return_address,
                    //           oparams, newoparams, oparams_size);

                    __xmhfhic_safepush(cpuid, src_slabid, dst_slabid, hic_calltype, return_address, oparams, newoparams, oparams_size, iparams_size);


                    //jump to destination slab entrystub
                    /*

                    RDI = newiparams
                    RSI = iparams_size
                    RDX = slab entrystub; used for SYSEXIT
                    RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
                    R8 = newoparams
                    R9 = oparams_size
                    R10 = src_slabid
                    R11 = cpuid

                    */

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
                        : "m" (newiparams),
                          "m" (iparams_size),
                          "m" (_xmhfhic_common_slab_info_table[dst_slabid].entrystub),
                          "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid]),
                          "m" (newoparams),
                          "m" (oparams_size),
                          "m" (src_slabid),
                          "m" (cpuid)
                        : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
                    );

                }
                break;

                case HIC_SLAB_X86VMXX86PC_GUEST:{
                    u32 errorcode;

                    //_XDPRINTF_("%s[%u]: going to invoke guest slab %u\n",
                    //           __FUNCTION__, (u32)cpuid, dst_slabid);
                    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VPID, dst_slabid+1);
                    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, _xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3);
                    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid]);
                    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, _xmhfhic_common_slab_info_table[dst_slabid].entrystub);

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

                }
                break;


                default:
                    _XDPRINTF_("%s[%u]: Unknown slabtype=%x. Halting!\n", __FUNCTION__, (u32)cpuid, hic_calltype);
                    HALT();

            }

        }
        break;


        case XMHF_HIC_SLABRET:{
            __xmhfhic_safestack_element_t elem;

            //pop tuple from safe stack
            __xmhfhic_safepop(cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.return_address,
                                &elem.oparams, &elem.newoparams, &elem.oparams_size, &elem.iparams_size);

            //_XDPRINTF_("%s[%u]: safepop: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x, ra=%016llx, \
            //           op=%016llx, newop=%016llx, opsize=%u\n",
            //        __FUNCTION__, (u32)cpuid,
            //           cpuid, elem.src_slabid, elem.dst_slabid, elem.hic_calltype, elem.return_address,
            //           elem.oparams, elem.newoparams, elem.oparams_size);

            //check to ensure this SLABRET is paired with a prior SLABCALL
            if ( !((elem.src_slabid == dst_slabid) && (elem.dst_slabid == src_slabid) && (elem.hic_calltype ==XMHF_HIC_SLABCALL)) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRET does not match prior SLABCALL. Halting!\n",
                    __FUNCTION__, (u32)cpuid);
                HALT();
            }


            //copy newoparams to internal buffer __paramsbuffer
            memcpy(&__paramsbuffer, elem.newoparams, (elem.oparams_size > 1024 ? 1024 : elem.oparams_size) );

            //adjust slab stack by popping off iparams_size and oparams_size
            _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtos[(u32)cpuid] += (elem.iparams_size+elem.oparams_size);

            //switch to destination slab page tables
            asm volatile(
                 "movq %0, %%rax \r\n"
                 "movq %%rax, %%cr3 \r\n"
                :
                : "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3)
                : "rax"
            );


            //copy internal buffer __paramsbuffer to oparams
            memcpy(elem.oparams, &__paramsbuffer, (elem.oparams_size > 1024 ? 1024 : elem.oparams_size) );

            //return back to slab
            /*
            RDI = undefined
            RSI = undefined
            RDX = return_address; for SYSEXIT
            RCX = return TOS; for SYSEXIT
            R8 = undefined
            R9 = undefined
            R10 = undefined
            R11 = undefined
            */

            asm volatile(
                 "movq %0, %%rdx \r\n"
                 "movq %1, %%rcx \r\n"

                 "sysexitq \r\n"
                 //"int $0x03 \r\n"
                 //"1: jmp 1b \r\n"
                :
                : "m" (elem.return_address),
                  "m" (_xmhfhic_common_slab_info_table[elem.src_slabid].archdata.slabtos[(u32)cpuid])
                : "rdx", "rcx"
            );

        }
        break;














        case XMHF_HIC_SLABCALLEXCEPTION:{
                slab_input_params_t *newiparams;
                slab_output_params_t *newoparams;

                //force destination slab to be the exception slab
                dst_slabid = XMHF_HYP_SLAB_XCEXHUB;

                //save return RSP
                _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtos[(u32)cpuid] = return_rsp;

                //copy iparams to internal buffer __paramsbuffer
                memcpy(&__paramsbuffer, iparams, (iparams_size > 1024 ? 1024 : iparams_size) );

                //switch to destination slab page tables
                asm volatile(
                     "movq %0, %%rax \r\n"
                     "movq %%rax, %%cr3 \r\n"
                    :
                    : "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3)
                    : "rax"
                );

                //make space on destination slab stack for iparams and copy iparams and obtain newiparams
                {
                    _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid] -= iparams_size;
                    newiparams = (slab_input_params_t *) _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid];
                    memcpy((void *)_xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid],
                           &__paramsbuffer, (iparams_size > 1024 ? 1024 : iparams_size) );
                }

                //push cpuid, src_slabid, dst_slabid, hic_calltype, return_address, iparams, new iparams and iparams_size tuple to
                //safe stack
                //_XDPRINTF_("%s[%u]: safepush: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x, ra=%016llx, \
                //           ip=%016llx, newip=%016llx, ipsize=%u\n",
                //        __FUNCTION__, (u32)cpuid,
                //           cpuid, src_slabid, dst_slabid, hic_calltype, return_address,
                //           iparams, newiparams, iparams_size);

                __xmhfhic_safepush(cpuid, src_slabid, dst_slabid, hic_calltype, return_address, iparams, newiparams, 0, iparams_size);


                //jump to exception slab entrystub
                /*

                RDI = newiparams
                RSI = iparams_size
                RDX = slab entrystub; used for SYSEXIT
                RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
                R8 = 0 (oparams)
                R9 = 0 (oparams_size)
                R10 = src_slabid
                R11 = cpuid

                */

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
                    : "m" (newiparams),
                      "m" (iparams_size),
                      "m" (_xmhfhic_common_slab_info_table[dst_slabid].entrystub),
                      "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid]),
                      "i" (0),
                      "i" (0),
                      "m" (src_slabid),
                      "m" (cpuid)
                    : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
                );

        }
        break;



        case XMHF_HIC_SLABRETEXCEPTION:{
            __xmhfhic_safestack_element_t elem;

            //check to ensure that we get SLABRETEXCEPTION only from the exception slab
            if ( !(src_slabid == XMHF_HYP_SLAB_XCEXHUB) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRETEXCEPTION from a non-exception slab. Halting!\n",
                    __FUNCTION__, (u32)cpuid);
                HALT();
            }

            //pop tuple from safe stack
            __xmhfhic_safepop(cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.return_address,
                                &elem.oparams, &elem.newoparams, &elem.oparams_size, &elem.iparams_size);

            //_XDPRINTF_("%s[%u]: safepop: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x, ra=%016llx, \
            //           op=%016llx, newop=%016llx, opsize=%u\n",
            //        __FUNCTION__, (u32)cpuid,
            //           cpuid, elem.src_slabid, elem.dst_slabid, elem.hic_calltype, elem.return_address,
            //           elem.oparams, elem.newoparams, elem.oparams_size);

            //check to ensure this SLABRETEXCEPTION is paired with a prior SLABCALLEXCEPTION
            if ( !((elem.src_slabid == dst_slabid) && (elem.dst_slabid == src_slabid) && (elem.hic_calltype ==XMHF_HIC_SLABCALLEXCEPTION)) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRETEXCEPTION does not match prior SLABCALLEXCEPTION. Halting!\n",
                    __FUNCTION__, (u32)cpuid);
                HALT();
            }

            //adjust slab stack by popping off iparams_size
            _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtos[(u32)cpuid] += (elem.iparams_size);

            //switch to destination slab page tables
            asm volatile(
                 "movq %0, %%rax \r\n"
                 "movq %%rax, %%cr3 \r\n"
                :
                : "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3)
                : "rax"
            );

            //return back to slab where exception originally occurred
            {
                    x86vmx_exception_frame_errcode_t *exframe = (x86vmx_exception_frame_errcode_t *)elem.oparams;
                    exframe->orig_rip = elem.return_address;

                    _XDPRINTF_("%s[%u]: returning from exception to %016llx\n",
                        __FUNCTION__, (u32)cpuid, exframe->orig_rip);

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
                        : "m" (exframe)
                        : "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
                          "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"

                    );

            }

        }
        break;















        case XMHF_HIC_SLABCALLINTERCEPT:{
            //force destination slab to be the intercept slab
            dst_slabid = XMHF_HYP_SLAB_XCIHUB;

            //_XDPRINTF_("%s[%u]: Trampoline Intercept call\n",
            //        __FUNCTION__, (u32)cpuid, read_rsp());

            //copy iparams (CPU GPR state) into arch. data for cpuid
            memcpy(&__xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
                   iparams, iparams_size);


            //push cpuid, src_slabid, dst_slabid, hic_calltype tuple to
            //safe stack
            //_XDPRINTF_("%s[%u]: safepush: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x\n",
            //        __FUNCTION__, (u32)cpuid,
            //           cpuid, src_slabid, dst_slabid, hic_calltype);

            __xmhfhic_safepush(cpuid, src_slabid, dst_slabid, hic_calltype, 0, 0, 0, 0, 0);


            //switch to destination slab page tables
            //XXX: eliminate this by preloading VMCS CR3 with xcihub CR3
            asm volatile(
                 "movq %0, %%rax \r\n"
                 "movq %%rax, %%cr3 \r\n"
                :
                : "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3)
                : "rax"
            );

            //intercept slab does not get any input parameters and does not
            //return any output parameters
            //jump to intercept slab entrystub
            /*

            RDI = newiparams (NULL)
            RSI = iparams_size (0)
            RDX = slab entrystub; used for SYSEXIT
            RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
            R8 = newoparams (NULL)
            R9 = oparams_size (0)
            R10 = src_slabid
            R11 = cpuid

            */

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
                  "m" (_xmhfhic_common_slab_info_table[dst_slabid].entrystub),
                  "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid]),
                  "i" (0),
                  "i" (0),
                  "m" (src_slabid),
                  "m" (cpuid)
                : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
            );

        }
        break;


        case XMHF_HIC_SLABRETINTERCEPT:{
            __xmhfhic_safestack_element_t elem;

            //check to ensure that we get SLABRETINTERCEPT only from the intercept slab
            if ( !(src_slabid == XMHF_HYP_SLAB_XCIHUB) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRETINTERCEPT from a non-intercept slab. Halting!\n",
                    __FUNCTION__, (u32)cpuid);
                HALT();
            }


            //pop tuple from safe stack
            __xmhfhic_safepop(cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.return_address,
                                &elem.oparams, &elem.newoparams, &elem.oparams_size, &elem.iparams_size);

            //_XDPRINTF_("%s[%u]: safepop: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x\n",
            //        __FUNCTION__, (u32)cpuid,
            //           cpuid, elem.src_slabid, elem.dst_slabid, elem.hic_calltype);

            //check to ensure this SLABRETINTERCEPT is paired with a prior SLABCALLINTERCEPT
            if ( !((elem.src_slabid == dst_slabid) && (elem.dst_slabid == src_slabid) && (elem.hic_calltype ==XMHF_HIC_SLABCALLINTERCEPT)) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRETINTERCEPT does not match prior SLABCALLINTERCEPT. Halting!\n",
                    __FUNCTION__, (u32)cpuid);
                HALT();
            }

            //resume caller (guest) slab where the intercept was triggered
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
                : "g" (&__xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs)
                : "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
                  "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp"

            );


        }
        break;
















        default:
            _XDPRINTF_("%s[%u]: Unknown hic_calltype=%x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, hic_calltype);
            HALT();


    }

    _XDPRINTF_("%s[%u]: Should never come here. Halting!\n",
                    __FUNCTION__, (u32)cpuid);
    HALT();
}








