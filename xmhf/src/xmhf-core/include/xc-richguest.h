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

// XMHF core richguest component 
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_RICHGUEST_H__
#define __XMHF_RICHGUEST_H__

#ifndef __ASSEMBLY__

void xmhf_richguest_initialize(xc_cpu_t *xc_cpu_bsp, xc_partition_t *xc_partition_richguest);
void xmhf_richguest_arch_initialize(xc_cpu_t *xc_cpu_bsp, xc_partition_t *xc_partition_richguest);

//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_walk_pagetables(context_desc_t context_desc, u32 vaddr);
u8 * xmhf_smpguest_arch_walk_pagetables(context_desc_t context_desc, u32 vaddr);

//----------------------------------------------------------------------
//rich guest memory functions

bool xmhf_smpguest_arch_readu16(context_desc_t context_desc, const void *guestaddress, u16 *valueptr);
bool xmhf_smpguest_arch_writeu16(context_desc_t context_desc, const void *guestaddress, u16 value);
bool xmhf_smpguest_arch_memcpyfrom(context_desc_t context_desc, void *buffer, const void *guestaddress, size_t numbytes);
bool xmhf_smpguest_arch_memcpyto(context_desc_t context_desc, void *guestaddress, const void *buffer, size_t numbytes);

#define xmhf_smpguest_readu16	xmhf_smpguest_arch_readu16
#define xmhf_smpguest_writeu16 xmhf_smpguest_arch_writeu16
#define xmhf_smpguest_memcpyfrom xmhf_smpguest_arch_memcpyfrom
#define xmhf_smpguest_memcpyto xmhf_smpguest_arch_memcpyto


#endif	//__ASSEMBLY__

#endif //__XMHF_RICHGUEST_H__
