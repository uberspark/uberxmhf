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

//  EMHF base platform component
//  addressing interface backends
//  authors: amit vasudevan (amitvasudevan@acm.org) and
//      jonathan m. mccune

#include <xmhf.h>

//functions to read/write memory using flat selector so that they
//can be used from both within the SL and runtime

#ifdef __AMD64__
u32 xmhf_baseplatform_arch_flat_va_offset = 0;

// find a virtual address from physical address
// in secure loader, ((-(fs << 21)) % 4GiB) for VA is 0 for GA
static void *xmhf_baseplatform_arch_flat_pa2va(u32 addr) {
    u32 physical_addr = (u32)addr - (u32)xmhf_baseplatform_arch_flat_va_offset;
    return (void*)(u64)physical_addr;
}
#elif !defined(__I386__)
    #error "Unsupported Arch"
#endif /* !defined(__I386__) */

//read 8-bits from absolute physical address
u8 xmhf_baseplatform_arch_flat_readu8(u32 addr){
#ifdef __AMD64__
    return *(u8*)(xmhf_baseplatform_arch_flat_pa2va(addr));
#elif defined(__I386__)
    u32 ret;
    __asm__ __volatile("xor %%eax, %%eax\r\n"
                       "movl %%fs:(%%ebx), %%eax\r\n"
                       : "=a"(ret)
                       : "b"(addr)
                       );
    return (u8)ret;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

//read 32-bits from absolute physical address
u32 xmhf_baseplatform_arch_flat_readu32(u32 addr){
#ifdef __AMD64__
    return *(u32*)(xmhf_baseplatform_arch_flat_pa2va(addr));
#elif defined(__I386__)
    u32 ret;
    __asm__ __volatile("xor %%eax, %%eax\r\n"
                       "movl %%fs:(%%ebx), %%eax\r\n"
                       : "=a"(ret)
                       : "b"(addr)
                       );
    return ret;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

//read 64-bits from absolute physical address
u64 xmhf_baseplatform_arch_flat_readu64(u32 addr){
#ifdef __AMD64__
    return *(u64*)(xmhf_baseplatform_arch_flat_pa2va(addr));
#elif defined(__I386__)
    u32 highpart, lowpart;
    __asm__ __volatile("xor %%eax, %%eax\r\n"
                       "xor %%edx, %%edx\r\n"
                       "movl %%fs:(%%ebx), %%eax\r\n"
                       "movl %%fs:0x4(%%ebx), %%edx\r\n"
                       : "=a"(lowpart), "=d"(highpart)
                       : "b"(addr)
                       );
    return  ((u64)highpart << 32) | (u64)lowpart;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

//write 32-bits to absolute physical address
void xmhf_baseplatform_arch_flat_writeu32(u32 addr, u32 val) {
#ifdef __AMD64__
    *(u32*)(xmhf_baseplatform_arch_flat_pa2va(addr)) = val;
#elif defined(__I386__)
    __asm__ __volatile__("movl %%eax, %%fs:(%%ebx)\r\n"
                         :
                         : "b"(addr), "a"((u32)val)
                         );
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

//write 64-bits to absolute physical address
void xmhf_baseplatform_arch_flat_writeu64(u32 addr, u64 val) {
#ifdef __AMD64__
    *(u64*)(xmhf_baseplatform_arch_flat_pa2va(addr)) = val;
#elif defined(__I386__)
    u32 highpart, lowpart;
    lowpart = (u32)val;
    highpart = (u32)((u64)val >> 32);

    __asm__ __volatile__("movl %%eax, %%fs:(%%ebx)\r\n"
                         "movl %%edx, %%fs:0x4(%%ebx)\r\n"
                         :
                         : "b"(addr), "a"(lowpart), "d"(highpart)
                         );
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

//memory copy from absolute physical address (src) to
//data segment relative address (dest)
void xmhf_baseplatform_arch_flat_copy(u8 *dest, u8 *src, u32 size){
    u32 i;
    u8 val;
    for(i=0; i < size; i++){
        val = xmhf_baseplatform_arch_flat_readu8((uintptr_t)src + i);
        dest[i] = val;
    }
}
