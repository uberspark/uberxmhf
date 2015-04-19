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

// XMHF slab decls./defns.
// author: amit vasudevan (amitvasudevan@acm.org)
// XXX: need to split arch. dependent portions

#ifndef __XMHFGEEC_H__
#define __XMHFGEEC_H__

#include <xmhf-hwm.h>
#include <xmhfhw.h>

/*
	1. XMHFGEEC_SLABTYPE_VfT_PROG_PRIME     -- verified trusted special prime slab
	2. XMHFGEEC_SLABTYPE_VfT_PROG           -- verified trusted (hypervisor) program slab
	3. XMHFGEEC_SLABTYPE_uVU_PROG           -- unverified untrusted (hypervisor) program slab
	4. XMHFGEEC_SLABTYPE_uVT_PROG           -- unverified trusted (hypervisor) program slab
	5. XMHFGEEC_SLABTYPE_uVU_PROG_GUEST     -- unverified untrusted (guest) program slab
	6. XMHFGEEC_SLABTYPE_uVT_PROG_GUEST     -- unverified trusted (guest) program slab
	7. XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST -- uverified untrusted richguest slab
*/


#define XMHFGEEC_SLABTYPE_VfT_PROG_PRIME        (0x10)
#define XMHFGEEC_SLABTYPE_VfT_PROG              (0x20)
#define XMHFGEEC_SLABTYPE_uVU_PROG              (0x30)
#define XMHFGEEC_SLABTYPE_uVT_PROG              (0x40)
#define XMHFGEEC_SLABTYPE_uVU_PROG_GUEST        (0x50)
#define XMHFGEEC_SLABTYPE_uVT_PROG_GUEST        (0x60)
#define XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST    (0x70)

#define XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_VfT_uVU_uVT_PROG_uVU_uVT_PROG_GUEST  (0x1)
#define XMHFGEEC_SENTINEL_CALL_EXCEPTION  (0x2)

#define HIC_SLAB_PHYSMEM_EXTENT_READ       (1 << 0)
#define HIC_SLAB_PHYSMEM_EXTENT_WRITE      (1 << 1)
#define HIC_SLAB_PHYSMEM_EXTENT_EXECUTE    (1 << 2)

#define HIC_SLAB_PHYSMEM_MAXEXTENTS         5


#ifndef __ASSEMBLY__

typedef void * slab_entrystub_t;


typedef u32 slab_privilegemask_t;
typedef u32 slab_callcaps_t;
typedef u32 slab_uapicaps_t;

typedef struct {
    u32 pci_bus;
    u32 pci_device;
    u32 pci_function;
    u32 vendor_id;
    u32 device_id;
}__attribute__((packed)) xc_platformdevice_arch_desc_t;


typedef struct {
	bool desc_valid;
	u32 numdevices;
    xc_platformdevice_arch_desc_t arch_desc[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) slab_platformdevices_t;


//slab capabilities type
typedef struct {
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    u32 slab_archparams;
} __attribute__((packed)) slab_caps_t;


#define HIC_SLAB_CALLCAP(x) (1 << x)
#define HIC_SLAB_UAPICAP(x) (1 << x)

//slab physical memory extent type
typedef struct {
    u32 addr_start;
    u32 addr_end;
    u32 protection;
} slab_physmem_extent_t;


//////
//modified data types
typedef struct {
	u32 slabtype; //hypervisor, guest
	bool mempgtbl_initialized;
	bool devpgtbl_initialized;
	u32 mempgtbl_cr3;
	u32 slabtos[MAX_PLATFORM_CPUS];
} __attribute__((packed)) x_slab_info_archdata_t;


typedef struct {
    x_slab_info_archdata_t archdata;
	bool slab_inuse;
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    slab_physmem_extent_t slab_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS];
	slab_entrystub_t entrystub;
} __attribute__((packed)) x_slab_info_t;


typedef struct {
    u32 slab_ctype;
    u32 src_slabid;
    u32 dst_slabid;
    u32 cpuid;
    u32 in_out_params[16];
} __attribute__((packed)) slab_params_t;

typedef struct {
    u32 reserved;
    u32 uapifn;
}__attribute__((packed)) xmhf_uapi_params_hdr_t;




void __slab_calltrampolinenew(slab_params_t *sp);


#define XMHF_SLAB_CALLNEW(sp) \
    __slab_calltrampolinenew(sp)




//////
// slab entry stub definitions
extern void slab_main(slab_params_t *sp);


#endif //__ASSEMBLY__


#endif //__XMHFGEEC_H__


