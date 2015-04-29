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

// XMHF/GEEC prime header file
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __GEEC_PRIME_H_
#define __GEEC_PRIME_H_



#ifndef __ASSEMBLY__

//MTRR memory type structure
struct _memorytype {
  u64 startaddr;
  u64 endaddr;
  u32 type;
  u32 invalid;
  u32 reserved[6];
} __attribute__((packed));


typedef struct {
    u8 pgtbl[3 * PAGE_SIZE_4K];
    u8 mlehdr[0x80];
} __attribute__((packed)) x86vmx_mle_header_t;

#define MAX_SLAB_MEMIOREGIONS_MEMEXTENTS (PCI_CONF_MAX_BARS * MAX_PLATFORM_DEVICES)
#define MAX_SLAB_MEMIOREGIONS_IOEXTENTS (PCI_CONF_MAX_BARS * MAX_PLATFORM_DEVICES)

#define _MEMIOREGIONS_EXTENTS_TYPE_MEM  0
#define _MEMIOREGIONS_EXTENTS_TYPE_IO   1
#define _MEMIOREGIONS_EXTENTS_TYPE_NONE 3

typedef struct {
    u32 extent_type;
    u32 addr_start;
    u32 addr_end;
} __attribute__((packed)) _memioregions_extents_t;

typedef struct {
    u32 num_memextents;
    u32 num_ioextents;
    _memioregions_extents_t memextents[MAX_SLAB_MEMIOREGIONS_MEMEXTENTS];
    _memioregions_extents_t ioextents[MAX_SLAB_MEMIOREGIONS_IOEXTENTS];
} __attribute__((packed)) slab_memioregions_t;


#define SYSDEV_MEMIOREGIONS_DTYPE_GENERAL   0
#define SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE    1
#define SYSDEV_MEMIOREGIONS_DTYPE_LAPIC     2
#define SYSDEV_MEMIOREGIONS_DTYPE_TPM       3
#define SYSDEV_MEMIOREGIONS_DTYPE_TXT       4
#define SYSDEV_MEMIOREGIONS_DTYPE_IOMMU     5

#define SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN   0xFF

typedef struct {
    u32 b;
    u32 d;
    u32 f;
    u16 vendor_id;
    u16 device_id;
    u32 dtype;
    _memioregions_extents_t memioextents[PCI_CONF_MAX_BARS];
} __attribute__((packed)) sysdev_memioregions_t;


extern __attribute__(( section(".data") )) XMHF_BOOTINFO *xcbootinfo;


void xmhfhic_arch_setup_slab_info(void);
void xmhfhic_arch_sanity_check_requirements(void);
void xmhfhic_arch_setup_slab_device_allocation(void);
void xmhfhic_arch_setup_slab_mem_page_tables(void);


CASM_FUNCDECL(void xmhfhic_arch_relinquish_control_to_init_slab(u64 cpuid, u64 entrystub, u64 mempgtbl_cr3, u64 slabtos));

#endif // __ASSEMBLY__


#endif /* __GEEC_PRIME_H_ */
