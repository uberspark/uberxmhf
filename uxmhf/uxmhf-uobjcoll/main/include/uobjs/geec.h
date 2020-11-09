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

#ifndef __GEEC_H__
#define __GEEC_H__

//#include <xmhf-hwm.h>
//#include <xmhfhw.h>

/*
	1. XMHFGEEC_SLABTYPE_VfT_PROG_PRIME     -- verified trusted special prime slab
	2. XMHFGEEC_SLABTYPE_VfT_PROG           -- verified trusted (hypervisor) program slab
	3. XMHFGEEC_SLABTYPE_uVU_PROG           -- unverified untrusted (hypervisor) program slab
	4. XMHFGEEC_SLABTYPE_uVT_PROG           -- unverified trusted (hypervisor) program slab
	5. XMHFGEEC_SLABTYPE_uVU_PROG_GUEST     -- unverified untrusted (guest) program slab
	6. XMHFGEEC_SLABTYPE_uVT_PROG_GUEST     -- unverified trusted (guest) program slab
	7. XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST -- uverified untrusted richguest slab
*/

#define XMHFGEEC_SLABTYPE_VfT_SENTINEL          (0x10)
#define XMHFGEEC_SLABTYPE_VfT_PROG              (0x20)
#define XMHFGEEC_SLABTYPE_uVU_PROG              (0x30)
#define XMHFGEEC_SLABTYPE_uVT_PROG              (0x40)
#define XMHFGEEC_SLABTYPE_uVU_PROG_GUEST        (0x50)
#define XMHFGEEC_SLABTYPE_uVT_PROG_GUEST        (0x60)
#define XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST    (0x70)




#define XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG                    (0)
#define XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG         (1)

#define XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG_GUEST   (2)
#define XMHFGEEC_SENTINEL_RET_VfT_PROG_TO_uVT_uVU_PROG          (3)

#define XMHFGEEC_SENTINEL_CALL_EXCEPTION                        (4)
#define XMHFGEEC_SENTINEL_RET_EXCEPTION                         (5)

#define XMHFGEEC_SENTINEL_CALL_INTERCEPT                        (6)
#define XMHFGEEC_SENTINEL_RET_INTERCEPT                         (7)

#define XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG         (8)
#define XMHFGEEC_SENTINEL_RET_uVT_uVU_PROG_TO_VfT_PROG          (9)


#define HIC_SLAB_PHYSMEM_EXTENT_READ       (1 << 0)
#define HIC_SLAB_PHYSMEM_EXTENT_WRITE      (1 << 1)
#define HIC_SLAB_PHYSMEM_EXTENT_EXECUTE    (1 << 2)

#define HIC_SLAB_PHYSMEM_MAXEXTENTS         4


#ifndef __ASSEMBLY__

typedef void * slab_entrystub_t;


typedef uint32_t slab_callcaps_t;
typedef uint32_t slab_uapicaps_t;
typedef uint32_t slab_memgrantreadcaps_t;
typedef uint32_t slab_memgrantwritecaps_t;
typedef uint32_t slab_memoffset_t;

/*
typedef struct {
    uint32_t pci_bus;
    uint32_t pci_device;
    uint32_t pci_function;
    uint32_t vendor_id;
    uint32_t device_id;
}__attribute__((packed)) xc_platformdevice_arch_desc_t;


typedef struct {
	bool desc_valid;
	uint32_t numdevices;
    xc_platformdevice_arch_desc_t arch_desc[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) slab_platformdevices_t;
*/

/*
//slab physical memory extent type
typedef struct {
    uint32_t addr_start;
    uint32_t addr_end;
    uint32_t protection;
} slab_physmem_extent_t;
*/

//slab device entry
typedef struct {
    uint32_t vendor_id;
    uint32_t device_id;
} slab_device_entry_t;

typedef struct {
	bool slab_inuse;
	uint32_t slabtype;
	//uint32_t mempgtbl_cr3;
	//uint32_t iotbl_base;
	uint32_t slabtos[MAX_PLATFORM_CPUS];
    slab_callcaps_t slab_callcaps;
    bool slab_uapisupported;
    slab_uapicaps_t slab_uapicaps[XMHFGEEC_TOTAL_SLABS];
    slab_memgrantreadcaps_t slab_memgrantreadcaps;
    slab_memgrantwritecaps_t slab_memgrantwritecaps;
    slab_device_entry_t incl_devices[XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES];
    uint32_t incl_devices_count;
    slab_device_entry_t excl_devices[XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES];
    uint32_t excl_devices_count;
    physmem_extent_t slab_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS];
    //slab_memoffset_t slab_memoffset_entries[XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES];
	slab_entrystub_t entrystub;
} __attribute__((packed)) xmhfgeec_slab_info_t;



#define XMHFGEEC_SLAB_CALLCAP_MASK(x)               (1UL << x)
#define XMHFGEEC_SLAB_UAPICAP_MASK(x)               (1UL << x)
#define XMHFGEEC_SLAB_MEMGRANTREADCAP_MASK(x)       (1UL << x)
#define XMHFGEEC_SLAB_MEMGRANTWRITECAP_MASK(x)      (1UL << x)


typedef struct {
    uint32_t slab_ctype;
    uint32_t src_slabid;
    uint32_t dst_slabid;
    uint32_t dst_uapifn;
    uint32_t cpuid;
    uint32_t in_out_params[16];
} __attribute__((packed)) slab_params_t;

/*typedef struct {
    uint32_t reserved;
    uint32_t uapifn;
}__attribute__((packed)) xmhf_uapi_params_hdr_t;
*/


/*@
	requires \valid(sp);
	assigns \nothing;
@*/
void __slab_callsentinel(slab_params_t *sp);


#define XMHF_SLAB_CALLNEW(sp) \
    __slab_callsentinel(sp)




//////
// slab entry stub definitions
CASM_FUNCDECL(void _slab_entrystub(slab_params_t *sp));

/////
// update to slab_main
extern void slab_main(slab_params_t *sp);
extern void ugcpust_slab_main(slab_params_t *sp);
extern void uhcpust_slab_main(slab_params_t *sp);
extern void uiotbl_slab_main(slab_params_t *sp);
extern void ugmpgtbl_slab_main(slab_params_t *sp);
extern void usysd_slab_main(slab_params_t *sp);
extern void uhmpgtbl_slab_main(slab_params_t *sp);
extern void xcexhub_slab_main(slab_params_t *sp);
extern void xcihub_slab_main(slab_params_t *sp);
extern void xc_init_slab_main(slab_params_t *sp);
extern void xcnwlog_slab_main(slab_params_t *sp);
extern void xhhyperdep_slab_main(slab_params_t *sp);
extern void xhsysclog_slab_main(slab_params_t *sp);




//////
// slab stack variable decls.
//////

extern __attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) uint8_t _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];
extern __attribute__ ((section(".stackhdr"))) uint32_t _slab_tos[MAX_PLATFORM_CPUS];


extern __attribute__((section(".data"))) __attribute__((aligned(4096))) xmhfgeec_slab_info_t xmhfgeec_slab_info_table[XMHFGEEC_TOTAL_SLABS];

#endif //__ASSEMBLY__


#endif //__GEEC_H__


