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
//#include <xmhf-core.h>
#include <xmhf-debug.h>

static void xmhf_xcphandler_arch_unhandled(u64 vector, x86regs64_t *r){
	x86idt64_stackframe_t *exframe = NULL;
    u64 errorcode=0;

    //grab and skip error code on stack if applicable
    //TODO: fixme, this won't hold if we call these exceptions with INT xx since there is no error code pushed
    //in such cases
	if(vector == CPU_EXCEPTION_DF ||
		vector == CPU_EXCEPTION_TS ||
		vector == CPU_EXCEPTION_NP ||
		vector == CPU_EXCEPTION_SS ||
		vector == CPU_EXCEPTION_GP ||
		vector == CPU_EXCEPTION_PF ||
		vector == CPU_EXCEPTION_AC){
		errorcode = *(u64 *)(r->rsp);
		r->rsp += sizeof(u64);
	}

    //get idt stack frame
    exframe = (x86idt64_stackframe_t *)r->rsp;

    //dump relevant info
	_XDPRINTF_("unhandled exception %x, halting!\n", vector);
	_XDPRINTF_("state dump:\n\n");
	_XDPRINTF_("errorcode=0x%016llx\n", errorcode);
	_XDPRINTF_("CS:RIP:RFLAGS = 0x%016llx:0x%016llx:0x%016llx\n", exframe->cs, exframe->rip, exframe->rflags);
	_XDPRINTF_("SS:RSP = 0x%016llx:0x%016llx\n", exframe->ss, exframe->rsp);
	_XDPRINTF_("CR0=0x%016llx, CR2=0x%016llx\n", read_cr0(), read_cr2());
	_XDPRINTF_("CR3=0x%016llx, CR4=0x%016llx\n", read_cr3(), read_cr4());
	_XDPRINTF_("CS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x\n", (u16)read_segreg_cs(), (u16)read_segreg_ds(), (u16)read_segreg_es(), (u16)read_segreg_ss());
	_XDPRINTF_("FS=0x%04x, GS=0x%04x\n", (u16)read_segreg_fs(), (u16)read_segreg_gs());
	_XDPRINTF_("TR=0x%04x\n", (u16)read_tr_sel());
	_XDPRINTF_("RAX=0x%016llx, RBX=0%016llx\n", r->rax, r->rbx);
	_XDPRINTF_("RCX=0x%016llx, RDX=0%016llx\n", r->rcx, r->rdx);
	_XDPRINTF_("RSI=0x%016llx, RDI=0%016llx\n", r->rsi, r->rdi);
	_XDPRINTF_("RBP=0x%016llx, RSP=0%016llx\n", r->rbp, r->rsp);
	_XDPRINTF_("R8=0x%016llx, R9=0%016llx\n", r->r8, r->r9);
	_XDPRINTF_("R10=0x%016llx, R11=0%016llx\n", r->r10, r->r11);
	_XDPRINTF_("R12=0x%016llx, R13=0%016llx\n", r->r12, r->r13);
	_XDPRINTF_("R14=0x%016llx, R15=0%016llx\n", r->r14, r->r15);

	//do a stack dump in the hopes of getting more info.
	{
		u64 i;
		u64 stack_start = r->rsp;
		_XDPRINTF_("\n-----stack dump (8 entries)-----\n");
		for(i=stack_start; i < stack_start+(8*sizeof(u64)); i+=sizeof(u64)){
			_XDPRINTF_("Stack(0x%016llx) -> 0x%016llx\n", i, *(u64 *)i);
		}
		_XDPRINTF_("\n-----stack dump end-------------\n");
	}
}

//==========================================================================================

//exception handler hub
bool xmhf_xcphandler_arch_hub(u64 vector, void *exdata){
    bool returnfromexcp=false;
    x86regs64_t *r = (x86regs64_t *)exdata;

	switch(vector){
			case 0x3:{
                xmhf_xcphandler_arch_unhandled(vector, r);
				_XDPRINTF_("%s: exception 3, returning\n", __FUNCTION__);
                returnfromexcp=true;
			}
			break;

			default:{
				xmhf_xcphandler_arch_unhandled(vector, r);
				_XDPRINTF_("\nHalting System!\n");
				returnfromexcp=false;
			}
	}

    return returnfromexcp;
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



#define XMHF_EXCEPTION_HANDLER_ADDROF(vector) &__xmhf_exception_handler_##vector

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

















/*entry into __xmhfhic_rtm_trampoline:
RDI = cpuid
RSI = iparams
RDX = iparams_size
RCX = oparams
R8 = oparams_size
R9 = dst_slabid
[RSP] = src_slabid
[RSP+8] = return_address
[RSP+16] = hic_calltype
*/




//HIC runtime exception stub
__attribute__((naked)) void __xmhfhic_rtm_exception_stub(void){

	asm volatile(												\
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

                        "movq %0, %%rdi \r\n"       //RDI=X86XMP_LAPIC_ID_MEMORYADDRESS
                        "movl (%%edi), %%edi\r\n"   //EDI(bits 0-7)=LAPIC ID
                        "shrl $24, %%edi\r\n"       //EDI=LAPIC ID
                        "movq __xmhfhic_x86vmx_cpuidtable+0x0(,%%edi,8), %%rdi\r\n" //RDI = 0-based cpu index for the CPU

                        "movq %%rsp, %%rsi \r\n"    //iparams
                        "movq $176, %%rdx \r\n"     //iparams_size

                        "movq %%rsp, %%rcx \r\n"    //oparams
                        "movq $176, %%r8 \r\n"      //oparams_size

                        "movq %1, %%r9 \r\n"        //dst_slabid

                        "movq 136(%%rsp), %%rax \r\n"
                        "pushq %2 \r\n"     //push hic_calltype
                        "pushq %%rax \r\n"  //push return_address
                                            //note: this does not take into account error code,
                                            //assumed that on any exception that includes an error
                                            //code we never get back to the caller
                        "movq %%cr3, %%rax \r\n"
                        "andq $0x00000000000FF000, %%rax \r\n"
                        "shr $12, %%rax \r\n"
                        "pushq %%rax \r\n"          //push source slab id


                        "callq __xmhfhic_rtm_trampoline \r\n"
					:
					: "i" (X86SMP_LAPIC_ID_MEMORYADDRESS),
                      "i" (XMHF_HYP_SLAB_HICTESTSLAB3),
					    "i" (XMHF_HIC_SLABCALLEXCEPTION)
                    :
		);
}



//HIC runtime trampoline stub
__attribute__((naked)) void __xmhfhic_rtm_trampoline_stub(void){

    asm volatile (
        "pushq %%rax \r\n"          //push call type
        "pushq %%r11 \r\n"          //push return address
        "movq %%cr3, %%rax \r\n"
        "andq $0x00000000000FF000, %%rax \r\n"
        "shr $12, %%rax \r\n"
        "pushq %%rax \r\n"          //push source slab id
       	"movq %0, %%rdi \r\n"       //RDI=X86XMP_LAPIC_ID_MEMORYADDRESS
		"movl (%%edi), %%edi\r\n"   //EDI(bits 0-7)=LAPIC ID
        "shrl $24, %%edi\r\n"       //EDI=LAPIC ID
        "movq __xmhfhic_x86vmx_cpuidtable+0x0(,%%edi,8), %%rdi\r\n" //RDI = 0-based cpu index for the CPU

        "callq __xmhfhic_rtm_trampoline \r\n"
      :
      : "i" (X86SMP_LAPIC_ID_MEMORYADDRESS)
      :
    );
}



//HIC runtime trampoline
void __xmhfhic_rtm_trampoline(u64 cpuid, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid, u64 src_slabid, u64 return_address, u64 hic_calltype){

    //_XDPRINTF_("%s[%u]: Trampoline got control: RSP=%016llx\n",
    //                __FUNCTION__, (u32)cpuid, read_rsp());

    //_XDPRINTF_("%s[%u]: Trampoline got control: cpuid=%u, iparams=%x, iparams_size=%u, \
    //           oparams=%x, oparams_size=%u, dst_slabid=%x, src_slabid=%x, return_address=%016llx \
    //           hic_calltype=%x\n",
    //                __FUNCTION__, (u32)cpuid, cpuid, iparams, iparams_size, oparams, oparams_size,
    //           dst_slabid, src_slabid, return_address, hic_calltype);

    switch(hic_calltype){
        case XMHF_HIC_SLABCALL:
        case XMHF_HIC_SLABCALLEXCEPTION:
            {
            //_XDPRINTF_("%s[%u]: safepush, return_address=%016llx\n",
            //        __FUNCTION__, (u32)cpuid, return_address);

            __xmhfhic_safepush(cpuid, src_slabid, dst_slabid, hic_calltype, return_address);


            //switch to destination slab page tables
            asm volatile(
                 "movq %0, %%rax \r\n"
                 "movq %%rax, %%cr3 \r\n"
                :
                : "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3)
                : "rax"
            );

            /*

            RDI = cpuid
            RSI = iparams
            RDX = for SYSEXIT
            RCX = for SYSEXIT
            R8 = oparams_size
            R9 = src_slabid
            R10 = iparams_size (original RDX)
            R11 = oparams (original RCX)*/

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
                : "m" (cpuid),
                  "m" (iparams),
                  "m" (_xmhfhic_common_slab_info_table[dst_slabid].entrystub),
                  "i" (0ULL),
                  "m" (oparams_size),
                  "m" (src_slabid),
                  "m" (iparams_size),
                  "m" (oparams)
                : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
            );

        }
        break;


        case XMHF_HIC_SLABRET:{
            __xmhfhic_safestack_element_t elem;
            __xmhfhic_safepop(cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.return_address);

            //_XDPRINTF_("%s[%u]: safepop, return_address=%016llx\n",
            //        __FUNCTION__, (u32)cpuid, elem.return_address);

            //switch to destination slab page tables
            asm volatile(
                 "movq %0, %%rax \r\n"
                 "movq %%rax, %%cr3 \r\n"
                :
                : "m" (_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3)
                : "rax"
            );

            switch(elem.hic_calltype){
                case XMHF_HIC_SLABCALL:{
                    /*

                    RDI = cpuid
                    RSI = iparams
                    RDX = for SYSEXIT
                    RCX = for SYSEXIT
                    R8 = oparams_size
                    R9 = dst_slabid
                    R10 = iparams_size (original RDX)
                    R11 = oparams (original RCX)*/

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
                        : "m" (cpuid),
                          "m" (iparams),
                          "m" (elem.return_address),
                          "i" (0ULL),
                          "m" (oparams_size),
                          "m" (dst_slabid),
                          "m" (iparams_size),
                          "m" (oparams)
                        : "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"
                    );
                }
                break;

                case XMHF_HIC_SLABCALLEXCEPTION:{
                    x86vmx_exception_frame_t *exframe = (x86vmx_exception_frame_t *)oparams;

                    _XDPRINTF_("%s[%u]: returning from exception: oparams=%016llx, oparams_size=%u\n",
                        __FUNCTION__, (u32)cpuid, oparams, oparams_size);

                    _XDPRINTF_("%s[%u]: original SS:RSP=%016llx:%016llx\n",
                        __FUNCTION__, (u32)cpuid, exframe->orig_ss, exframe->orig_rsp);

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
                        "addq $8, %%rsp \r\n"
                        "iretq \r\n"
                        :
                        : "m" (oparams)
                        : "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
                          "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"

                    );

                }
                break;

            }


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

