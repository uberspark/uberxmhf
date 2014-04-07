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

// platform memory access interface 
// any memory access which is not part of the xmhf framework should
// use these interfaces
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __MEMACCESS_H__
#define __MEMACCESS_H__


#ifndef __ASSEMBLY__


#ifndef __XMHF_VERIFICATION__
	// Note: since we are unity mapped, runtime VA = system PA

	//hypervisor runtime virtual address to secure loader address
	static inline void * hva2sla(void *hva){
		return (void*)((u32)hva);	
	}
	
	//secure loader address to system physical address
	static inline spa_t sla2spa(void *sla){
		return (spa_t) ((u32)sla );
	}
	
	// XMHF runtime virtual-address to system-physical-address and vice-versa
	static inline spa_t hva2spa(void *hva){
		uintptr_t hva_ui = (uintptr_t)hva;
		return hva_ui;
	}
	  
	static inline void * spa2hva(spa_t spa){
		return (void *)(uintptr_t)spa;
	}
	
	static inline spa_t gpa2spa(gpa_t gpa) { return gpa; }
	static inline gpa_t spa2gpa(spa_t spa) { return spa; }
	static inline void* gpa2hva(gpa_t gpa) { return spa2hva(gpa2spa(gpa)); }
	static inline gpa_t hva2gpa(hva_t hva) { return spa2gpa(hva2spa(hva)); }

#else //__XMHF_VERIFICATION__

	static inline void * hva2sla(void *hva){ return (void*)((u32)hva);	}
	static inline spa_t sla2spa(void *sla){	return (spa_t) ((u32)sla ); }
	#define hva2spa(x) (u32)(x)
	static inline void * spa2hva(spa_t spa) { (void *)(uintptr_t)(spa); }
	static inline spa_t gpa2spa(gpa_t gpa) { return gpa; }
	static inline gpa_t spa2gpa(spa_t spa) { return spa; }
	static inline void* gpa2hva(gpa_t gpa) { return spa2hva(gpa2spa(gpa)); }
	static inline gpa_t hva2gpa(hva_t hva) { return spa2gpa(hva2spa(hva)); }	

#endif //__XMHF_VERIFICATION__


//functions to read/write memory from "system physical address"
//all reads and writes to non-framework memory areas (e.g., BIOS
//data areas, MMIO, rich guest memory etc.) should finally end up
//here

//read 8-bits from absolute physical address
static inline u8 xmhf_baseplatform_arch_flat_readu8(u32 addr){
/*    u32 ret;
    __asm__ __volatile("xor %%eax, %%eax\r\n"        
                       "movl %%fs:(%%ebx), %%eax\r\n"
                       : "=a"(ret)
                       : "b"(addr)
                       );
    return (u8)ret;        
*/
    u8 *valueptr = (u8 *)addr;
    u8 value = *valueptr;
    return value;
}

//read 16-bits from absolute physical address
static inline u16 xmhf_baseplatform_arch_flat_readu16(u32 addr){
/*    u32 ret;
    __asm__ __volatile("xor %%eax, %%eax\r\n"        
                       "movl %%fs:(%%ebx), %%eax\r\n"
                       : "=a"(ret)
                       : "b"(addr)
                       );
    return ret;        */
    u16 *valueptr = (u16 *)addr;
    u16 value = *valueptr;
    return value;
}

//read 32-bits from absolute physical address
static inline u32 xmhf_baseplatform_arch_flat_readu32(u32 addr){
/*    u32 ret;
    __asm__ __volatile("xor %%eax, %%eax\r\n"        
                       "movl %%fs:(%%ebx), %%eax\r\n"
                       : "=a"(ret)
                       : "b"(addr)
                       );
    return ret;        */
    u32 *valueptr = (u32 *)addr;
    u32 value = *valueptr;
    return value;
}

//read 64-bits from absolute physical address
static inline u64 xmhf_baseplatform_arch_flat_readu64(u32 addr){
/*    u32 highpart, lowpart;
    __asm__ __volatile("xor %%eax, %%eax\r\n"        
    									 "xor %%edx, %%edx\r\n"
                       "movl %%fs:(%%ebx), %%eax\r\n"
                       "movl %%fs:0x4(%%ebx), %%edx\r\n"
                       : "=a"(lowpart), "=d"(highpart)
                       : "b"(addr)
                       );
    return  ((u64)highpart << 32) | (u64)lowpart;        */
    u64 *valueptr = (u64 *)addr;
    u64 value = *valueptr;
    return value;
}

//write 32-bits to absolute physical address
static inline void xmhf_baseplatform_arch_flat_writeu32(u32 addr, u32 val) {
/*    __asm__ __volatile__("movl %%eax, %%fs:(%%ebx)\r\n"
                         :
                         : "b"(addr), "a"((u32)val)
                         );
*/
    u32 *valueptr = (u32 *)addr;
    *valueptr = val;
}

//write 64-bits to absolute physical address
static inline void xmhf_baseplatform_arch_flat_writeu64(u32 addr, u64 val) {
/*    u32 highpart, lowpart;
    lowpart = (u32)val;
    highpart = (u32)((u64)val >> 32);
    
		__asm__ __volatile__("movl %%eax, %%fs:(%%ebx)\r\n"
												"movl %%edx, %%fs:0x4(%%ebx)\r\n"	
                         :
                         : "b"(addr), "a"(lowpart), "d"(highpart)
                         );
*/
    u64 *valueptr = (u64 *)addr;
    *valueptr = val;
}

//memory copy from absolute physical address (src) to
//data segment relative address (dest)
static inline void xmhf_baseplatform_arch_flat_copy(u8 *dest, u8 *src, u32 size){
/*	u32 i;
	u8 val;
	for(i=0; i < size; i++){
		val = xmhf_baseplatform_arch_flat_readu8((u32)src + i);
		dest[i] = val;
	}*/
	memcpy(dest, src, size);
}


#endif	//__ASSEMBLY__

#endif //__MEMACCESS_H__
