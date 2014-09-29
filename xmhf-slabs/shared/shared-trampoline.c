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
#include <xmhf-core.h>
#include <xmhf-debug.h>

/*// esi = 32-bit address of input parameter base
// edi = 32-bit address of return from slab call
// ebp = 32-bit address of destination slab entry point
// ecx = top 16-bits = size of result dwords
//		 bottom 16-bits = size of parameter dwords
// ebx = 32-bit function number
// eax = 32-bit src slab macmid
// edx = 32-bit dst slab macmid

__attribute__((naked)) __attribute (( section(".slabtrampoline") )) void _slab_trampoline(void){

	asm volatile(
			//"int $0x03 \r\n"

			"movl %%edx, %%cr3 \r\n"				//load callee MAC
			"pushl %%esi \r\n"						//save caller parameter base address
			"pushl %%eax \r\n"						//save caller MAC
			"pushl %%edi \r\n" 						//save caller return address
			"pushl %%ecx \r\n"						//save caller param/ret count

			"movl %%ebp, %%eax \r\n"				//eax= callee entry point

			//"int $0x03 \r\n"

			"xorl %%ebp, %%ebp \r\n"				//zero out %ebp so we can use it to keep track of stack frame

			"xorl %%edx, %%edx \r\n"				//edx=0
			"movw %%cx, %%dx \r\n"					//edx=parameter dwords
			"shr $16, %%ecx \r\n"					//ecx=result dwords

			//"int $0x03 \r\n"

			"cmpl $0, %%ecx \r\n"					//check if we are supporting aggregate return type for this slab call
			"je 1f \r\n"							//if no, then skip aggregate return type stack frame adjustment

			"movl %%ecx, %%ebp \r\n"				//ebp=result dwords
			"movl %%esp, %%ecx \r\n"				//ecx=top of stack
			"subl %%ebp, %%ecx \r\n"				//ecx=top of stack (32-bit address of aggregate return type bufffer)
			"addl $4, %%esi	\r\n"					//skip the caller aggregate return type buffer pointer on input parameter list
													//we will create a new stack frame for our return type buffer pointer
			"subl $4, %%edx \r\n"					//reduce parameter size by 1 dword to account for the aggregate return type buffer pointer

			//"int $0x03 \r\n"

			"1:\r\n"
			"addl %%edx, %%ebp \r\n"				//ebp=parameter + result dwords
			"subl %%ebp, %%esp 	\r\n"				//adjust top of stack to accomodate input parameters and aggregate return type buffer (if applicable)
			"movl %%esp, %%edi \r\n"				//edi=top of stack (with room made for input parameters)

			"xchg %%ecx, %%edx \r\n"
			"cld \r\n"								//clear direction flag to copy forward
			"rep movsb \r\n"						//copy input parameters (at esi) to top of stack
			"xchg %%ecx, %%edx \r\n"

			//"int $0x03 \r\n"

			"cmpl $0, %%ecx \r\n"					//if we have aggregate return type then we need to push the aggregate return type buffer address
			"je 1f \r\n"							//if not, then invoke the callee slab entry point
			"pushl %%ecx \r\n"						//push our new return type buffer address that we have just made space for in our new call frame
			"movl %%ecx, %%esi \r\n"				//esi= 32-bit address of aggregate return type buffer which we will use to copy back return value

			"1: call *%%eax \r\n"					//invoke callee slab entry point

			"addl %%ebp, %%esp \r\n"				//discard callee stack frame that we created

			"popl %%ecx \r\n"						//ecx = caller param/return size
			"popl %%ebp \r\n"						//ebp = caller return address
			"popl %%ebx \r\n"						//ebx = caller MAC

			"movl %%ebx, %%cr3 \r\n"				//load caller MAC

			"popl %%edi \r\n"						//edi = caller parameter base address
			"movl (%%edi), %%edi \r\n"				//edi = caller aggregate return type buffer

			"shr $16, %%ecx \r\n"					//ecx = result size
			"cld \r\n"
			"rep movsb \r\n"						//store aggregate return value (if any)

			"jmpl *%%ebp \r\n"						//go back to caller
		:
		:
		:
	);


}

//--------------------------------------------------------------------
*/


__attribute (( section(".slabtrampoline") )) void _slab_trampolinenew(u64 rsv0, u64 src_slabid, u64 dst_slabid, u64 call_type, u64 rsv1, u64 rsv2){

    //_XDPRINTF_("%s: got control: src slabid=%u, dst slabid=%u, call_type=%u\n",
    //            __FUNCTION__, src_slabid, dst_slabid, call_type);


    /*asm volatile (
        "movq %%cr3, %%rax \r\n"
        "movq $0x8000000000000000, %%r8 \r\n"
        "orq %%r8, %%rax \r\n"
        "movq %%rax, %%cr3 \r\n"
        :
        :
        : "rax"
    );*/


    asm volatile (
        "movq %0, %%rdi \r\n"
        "movq %1, %%rsi \r\n"
        "movq %2, %%rdx \r\n"
        "movq %3, %%rcx \r\n"
		"movq %%rbp, %%rsp \r\n"
		"movq (%%rsp), %%rbp \r\n"
		"addq $8, %%rsp \r\n"
        "movq %4, %%r8 \r\n"
        "jmp *%%r8 \r\n"
        :
        : "m" (rsv0), "m" (src_slabid), "m" (dst_slabid),
          "m" (call_type), "m" (_slab_table[dst_slabid].entry_cr3_new)
        : "rdi", "rsi", "rdx", "rcx", "rsp", "rbp", "r8"
    );

    ////debug
    //_XDPRINTF_("Halting!\n");
    //_XDPRINTF_("XMHF Tester Finished!\n");
    //HALT();

}





#if 0

//parameter-1: in ecx = struct *
//parameter-2: in edx = parameter size/opcall
//note: the compiler will setup the prolog which will make ebp point to the stack pointer
//that we entered on. we use this to restore the stack back to what it was before transferring
//control to the destination slab
//e.g., movl %%ebp, %%esp
//		movl (%esp), %%ebp
//		addl $4, %%esp

__attribute__((fastcall)) __attribute (( section(".slabtrampoline") )) void _slab_trampolinenew(slab_trampoline_frame_t *tframe, u32 framesize_op){
	u32 aggrettypeptr;

	//_XDPRINTF_("%s: got control\n", __FUNCTION__);
	//_XDPRINTF_(" returnaddress=%08x, framesize_op=%08x, src_slabid=%u, dst_slabid=%u, fn_id=%u\n",
	//	tframe->returnaddress, framesize_op, tframe->src_slabid, tframe->dst_slabid, tframe->fn_id);


	//{
	//		u32 *p, i;
	//		p = (u32 *)&tframe->params;
	//		_XDPRINTF_("%s: %u, %u, %u, %u\n", __FUNCTION__, p[0], p[1], p[2], p[3]);
	//
	//}

/*
	//switch to destination slab MAC
	asm volatile(
    	"movl %0, %%eax \r\n"
		"movl %%eax, %%cr3 \r\n"
		:
		: "m" (_slab_table[tframe->dst_slabid].slab_macmid)
		: "eax"
	);
*/
	//_XDPRINTF_("%s: dst CR3 loaded, proceeding with call, cr3=%08x, EP=%08x\n", __FUNCTION__, read_cr3(), _slab_table[tframe->dst_slabid].entry_cr3_new);

/*
	//call destination slab entry point
	asm volatile(
    	"movl %1, %%esi \r\n"
		"movl %2, %%ecx \r\n"
		"movl %3, %%eax \r\n"
		"call *%%eax \r\n"
		"movl %%esi, %0 \r\n"
		: "=S" (aggrettypeptr)
		: "g" (&tframe->src_slabid), "g" (framesize_op), "m" (_slab_table[tframe->dst_slabid].entry_cr3_new)
		: "esi", "ecx"
	);
*/
	//{
	//
	//	slab_retval_t *r;
	//	_XDPRINTF_("%s: aggrettypeptr=%08x\n", __FUNCTION__, aggrettypeptr);
	//	r = (slab_retval_t *)aggrettypeptr;
	//	_XDPRINTF_("%s: retval=%u", __FUNCTION__, r->retval_u32);
	//}

	//_XDPRINTF_("%s: came back from dst call\n", __FUNCTION__);
/*
	//switch back to source slab MAC
	asm volatile(
		"movl %0, %%eax \r\n"
		"movl %%eax, %%cr3 \r\n"
		:
		: "m" (_slab_table[tframe->src_slabid].slab_macmid)
		: "eax"
	);
*/
	//_XDPRINTF_("%s: going back to src slab, cr3 reloaded to %08x\n", __FUNCTION__, read_cr3());


/*	//return back to source slab
	asm volatile(
		"movl %0, %%esi \r\n"
		"movl %1, %%eax \r\n"
		"movl %%ebp, %%esp \r\n"
		"movl (%%esp), %%ebp \r\n"
		"addl $4, %%esp \r\n"
		"jmpl *%%eax \r\n"
		:
		: "m" (aggrettypeptr), "m" (tframe->returnaddress)
		:
	);
*/

	//_XDPRINTF_("%s: Halting, aggrettypeptr=%08x!\n", __FUNCTION__, aggrettypeptr);
	//HALT();
}

#endif // 0
