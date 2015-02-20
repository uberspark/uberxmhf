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

//xmhfhw_cpu_mem: CPU platform memory access interface (sysmem)
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>


// Note: since we are unity mapped, runtime VA = system PA

//hypervisor runtime virtual address to secure loader address
void * hva2sla(void *hva){
    return (void*)((u32)hva);
}

//secure loader address to system physical address
spa_t sla2spa(void *sla){
    return (spa_t) ((u32)sla );
}

// XMHF runtime virtual-address to system-physical-address and vice-versa
spa_t hva2spa(void *hva){
    uintptr_t hva_ui = (uintptr_t)hva;
    return hva_ui;
}

void * spa2hva(spa_t spa){
    return (void *)(uintptr_t)spa;
}

spa_t gpa2spa(gpa_t gpa)
{
        return gpa;
}

gpa_t spa2gpa(spa_t spa){
        return spa;
}

void* gpa2hva(gpa_t gpa){
        return spa2hva(gpa2spa(gpa));
}

gpa_t hva2gpa(hva_t hva){
        return spa2gpa(hva2spa(hva));
}


//functions to read/write memory from "system physical address"
//all reads and writes to non-framework memory areas (e.g., BIOS
//data areas, MMIO, rich guest memory etc.) should finally end up
//here

//read 8-bits from absolute physical address
u8 xmhfhw_sysmemaccess_readu8(u32 addr){
    u8 *valueptr = (u8 *)addr;
    u8 value = *valueptr;
    return value;
}

//read 16-bits from absolute physical address
u16 xmhfhw_sysmemaccess_readu16(u32 addr){
    u16 *valueptr = (u16 *)addr;
    u16 value = *valueptr;
    return value;
}

//read 32-bits from absolute physical address
u32 xmhfhw_sysmemaccess_readu32(u32 addr){
    u32 *valueptr = (u32 *)addr;
    u32 value = *valueptr;
    return value;
}

//read 64-bits from absolute physical address
u64 xmhfhw_sysmemaccess_readu64(u32 addr){
    u64 *valueptr = (u64 *)addr;
    u64 value = *valueptr;
    return value;
}


//write 8-bits to absolute physical address
void xmhfhw_sysmemaccess_writeu8(u32 addr, u8 val) {
    u8 *valueptr = (u8 *)addr;
    *valueptr = val;
}

//write 16-bits to absolute physical address
void xmhfhw_sysmemaccess_writeu16(u32 addr, u16 val) {
    u16 *valueptr = (u16 *)addr;
    *valueptr = val;
}

//write 32-bits to absolute physical address
void xmhfhw_sysmemaccess_writeu32(u32 addr, u32 val) {
    u32 *valueptr = (u32 *)addr;
    *valueptr = val;
}

//write 64-bits to absolute physical address
void xmhfhw_sysmemaccess_writeu64(u32 addr, u64 val) {
    u64 *valueptr = (u64 *)addr;
    *valueptr = val;
}

//the following function can be used to write to framework data areas
//only. e.g., copying from rich guest to hypapp data buffer
//memory copy from absolute physical address (src) to
//absolute physical address (dest)
//TODO: ensure dest does not fall within framework code regions
void xmhfhw_sysmemaccess_copy(u8 *dest, u8 *src, u32 size){
	memcpy(dest, src, size);
}


