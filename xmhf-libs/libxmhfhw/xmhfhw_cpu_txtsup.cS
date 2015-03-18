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

// xmhfhw_cpu_txt: CPU TXT functions
// authors: amit vasudevan (amitvasudevan@acm.org) and jonmccune@cmu.edu

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>


/*
 * fns to read/write TXT config regs
 *
 */

__attribute__((naked)) uint64_t read_config_reg(uint32_t config_regs_base, uint32_t reg)
{
    /* these are MMIO so make sure compiler doesn't optimize */
    //return *(volatile uint64_t *)(unsigned long)(config_regs_base +
    //reg);

//    u64 ret;
//    u32 addr = config_regs_base + reg;
//    __asm__ __volatile__("movl (%%ebx), %%eax\r\n"
//                         "movl 4(%%ebx), %%edx\r\n"
//                         : "=A"(ret)
//                         : "b"(addr)
//                         );
//    return ret;
    asm volatile ("movl 0x4(%esp), %ecx \r\n"); //ecx = config_regs_base
    asm volatile ("addl 0x8(%esp), %ecx \r\n"); //ecx = config_regs_base + reg
    asm volatile ("movl (%ecx), %eax \r\n");
    asm volatile ("movl 0x4(%ecx), %edx \r\n"); //edx:eax = 64-bit val
    asm volatile ("ret \r\n");


}

__attribute__((naked)) void write_config_reg(uint32_t config_regs_base, uint32_t reg,
                                    uint64_t val)
{
    /* these are MMIO so make sure compiler doesn't optimize */
    //*(volatile uint64_t *)(unsigned long)(config_regs_base + reg) =
    //val;
    //u32 addr = config_regs_base + reg;

    //__asm__ __volatile__("movl %%eax, (%%ebx)\r\n"
    //                     "movl %%edx, 4(%%ebx)\r\n"
    //                     :
    //                     : "A"(val), "b"(addr)
    //                     );

    asm volatile ("movl 0x4(%esp), %ecx \r\n"); //ecx = config_regs_base
    asm volatile ("addl 0x8(%esp), %ecx \r\n"); //ecx = config_regs_base + reg
    asm volatile ("movl 0xC(%esp), %eax \r\n");
    asm volatile ("movl 0x10(%esp), %edx \r\n"); //edx:eax = val
    asm volatile ("movl %eax, (%ecx) \r\n");
    asm volatile ("movl %edx, 0x4(%ecx) \r\n");
    asm volatile ("ret \r\n");

}



__attribute__((naked)) void xmhfhw_cpu_getsec(u32 *eax, //0xC
                                              u32 *ebx, //0x10
                                              u32 *ecx, //0x14
                                              u32 *edx){ //0x18


    asm volatile ("pushl %esi \r\n");
    asm volatile ("pushl %ebx \r\n");

    asm volatile ("movl 0xC(%esp), %eax \r\n");
    asm volatile ("movl (%eax), %eax \r\n");
    asm volatile ("movl 0x10(%esp), %ebx \r\n");
    asm volatile ("movl (%ebx), %ebx \r\n");
    asm volatile ("movl 0x14(%esp), %ecx \r\n");
    asm volatile ("movl (%ecx), %ecx \r\n");
    asm volatile ("movl 0x18(%esp), %edx \r\n");
    asm volatile ("movl (%edx), %edx \r\n");

    asm volatile (IA32_GETSEC_OPCODE "\r\n");

    asm volatile ("movl 0xC(%esp), %esi \r\n");
    asm volatile ("movl %eax, (%esi) \r\n");
    asm volatile ("movl 0x10(%esp), %esi \r\n");
    asm volatile ("movl %ebx, (%esi) \r\n");
    asm volatile ("movl 0x14(%esp), %esi \r\n");
    asm volatile ("movl %ecx, (%esi) \r\n");
    asm volatile ("movl 0x18(%esp), %esi \r\n");
    asm volatile ("movl %edx, (%esi) \r\n");

    asm volatile ("popl %ebx \r\n");
    asm volatile ("popl %esi \r\n");
    asm volatile ("ret \r\n");

/*    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
			  : "=a" (*eax),
                "=b" (*ebx),
                "=c" (*ecx),
                "=d" (*edx)
			  : "a"(*eax),
			    "b"(*ebx),
			    "c"(*ecx),
			    "d"(*edx)
              : "eax", "ebx", "ecx", "edx"
              );
*/


/*    asm volatile ("pushl %ebx \r\n");
    asm volatile ("pushl %esi \r\n");

    asm volatile ("movl 0x8(%esp), %ebx \r\n"); //ebx = index
    asm volatile ("movl $" IA32_GETSEC_PARAMETERS ", %eax \r\n"); //eax = IA32_GETSEC_PARAMETERS
    asm volatile (IA32_GETSEC_OPCODE "\r\n");
    asm volatile ("cmpl 0x10(%esp), 0 \r\n");
    asm volatile ("jz gp1 \r\n");
    asm volatile ("movl %eax, ")
    asm volatile ("popl %ebx \r\n");
    asm volatile ("ret \r\n");
*/

}


