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

// XMHF HWM MMIO VTd decls.
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHFHWM_VTD_H___
#define __XMHFHWM_VTD_H___

#define VTD_DMAR_SIGNATURE  (0x52414D44) //"DMAR"
#define VTD_MAX_DRHD   8		//maximum number of DMAR h/w units

//VT-d register offsets (sec. 10.4, Intel_VT_for_Direct_IO)
#define VTD_VER_REG_OFF 		0x000				//arch. version (32-bit)
#define VTD_CAP_REG_OFF 		0x008				//h/w capabilities (64-bit)
#define VTD_ECAP_REG_OFF  	0x010				//h/w extended capabilities (64-bit)
#define VTD_GCMD_REG_OFF  	0x018				//global command (32-bit)
#define VTD_GSTS_REG_OFF  	0x01C				//global status (32-bit)
#define VTD_RTADDR_REG_OFF  0x020				//root-entry table address (64-bit)
#define VTD_CCMD_REG_OFF  	0x028				//manage context-entry cache (64-bit)
#define VTD_FSTS_REG_OFF  	0x034				//report fault/error status (32-bit)
#define VTD_FECTL_REG_OFF 	0x038				//interrupt control (32-bit)

#define VTD_PMEN_REG_OFF  	0x064				//enable DMA protected memory regions (32-bits)

#define VTD_PLMBASE_REG_OFF	0x068				//protected low memory base register (32-bits)
#define VTD_PLMLIMIT_REG_OFF	0x6C			//protected low memory limit register (32-bits)

#define VTD_PHMBASE_REG_OFF	0x070				//protected high memory base register (64-bits)
#define VTD_PHMLIMIT_REG_OFF	0x78			//protected high memory limit register (64-bits)

#define VTD_IVA_REG_OFF  		0x0DEAD  		//invalidate address register (64-bits)
																				//note: the offset of this register is computed
                                    		//at runtime for a specified DMAR device
#define VTD_IOTLB_REG_OFF   0x0BEEF     //IOTLB invalidate register (64-bits)
																				//note: the offset is VTD_IVA_REG_OFF + 8 and
																				//computed at runtime for a specified DMAR device


//VT-d register access types (custom definitions)
#define VTD_REG_READ  			0xaa				//read VTD register
#define VTD_REG_WRITE 			0xbb				//write VTD register

//Vt-d register access widths (custom definitions)
#define VTD_REG_32BITS  		0x32ff
#define VTD_REG_64BITS  		0x64ff

//Vt-d page-table bits
#define VTD_RET_PRESENT                     (1UL << 0)
#define VTD_CET_PRESENT                     (1UL << 0)
#define VTD_PAGE_READ						(1UL << 0)
#define VTD_PAGE_WRITE						(1UL << 1)
#define VTD_PAGE_EXECUTE                    (1UL << 2)
#define VTD_PAGE_SUPER      			    (1UL << 7)

//vt-d page table page walk lengths
#define VTD_PAGEWALK_3LEVEL     (0x3)
#define VTD_PAGEWALK_4LEVEL     (0x4)
#define VTD_PAGEWALK_NONE       (0x0)

#define VTD_RET_MAXPTRS         (256)
#define VTD_CET_MAXPTRS         (256)

//vt-d page table max entries
#define VTD_PTRS_PER_PML4T          1
#define VTD_MAXPTRS_PER_PML4T       512

#define VTD_PTRS_PER_PDPT           4
#define VTD_MAXPTRS_PER_PDPT        512

#define VTD_PTRS_PER_PDT            512

#define VTD_PTRS_PER_PT             512



#ifndef __ASSEMBLY__

//Vt-d DMAR structure
//sizeof(VTD_DMAR) = 48 bytes
typedef struct{
  u32 signature;
  u32 length;
  u8 revision;
  u8 checksum;
  u8 oemid[6];
  u64 oemtableid;
	u32 oemrevision;
	u32 creatorid;
	u32 creatorrevision;
  u8 hostaddresswidth;
  u8 flags;
  u8 rsvdz[10];
}__attribute__ ((packed)) VTD_DMAR;



//VT-d DMAR table DRHD structure
//sizeof(VTD_DMAR_DRHD) = 16 bytes
typedef struct{
  u16 type;
  u16 length;
  u8 flags;
  u8 rsvdz0;
  u16 pcisegment;
  u64 regbaseaddr;
}__attribute__ ((packed)) VTD_DMAR_DRHD;


//VT-d DRHD structure
typedef struct{
  u16 type;
  u16 length;
  u8 flags;
  u8 rsvdz0;
  u16 pcisegment;
  u64 regbaseaddr;
  u32 iotlb_regaddr;    //not part of ACPI structure
  u32 iva_regaddr;      //not part of ACPI structure
}__attribute__ ((packed)) VTD_DRHD;

typedef u32 vtd_drhd_handle_t;

typedef struct {
    u64 qwords[2];
} __attribute__((packed)) vtd_ret_entry_t;

#define vtd_make_rete(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1)))) | (u64)(flags)

typedef struct {
    u64 qwords[2];
} __attribute__((packed)) vtd_cet_entry_t;

#define vtd_make_cete(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1)))) | (u64)(flags)

#define vtd_make_cetehigh(address_width, domain_id) \
  (((u64)domain_id & 0x000000000000FFFFULL) << 7) | ((u64)(address_width) & 0x0000000000000007ULL)


typedef u64 vtd_pml4te_t;
typedef u64 vtd_pdpte_t;
typedef u64 vtd_pdte_t;
typedef u64 vtd_pte_t;


/* make a pml4 entry from individual fields */
#define vtd_make_pml4te(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1)))) | (u64)(flags)

/* make a page directory pointer entry from individual fields */
#define vtd_make_pdpte(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1)))) | (u64)(flags)

/* make a page directory entry for a 4KB page from individual fields */
#define vtd_make_pdte(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1)))) | (u64)(flags)

/* make a page table entry from individual fields */
#define vtd_make_pte(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1)))) | (u64)(flags)



//------------------------------------------------------------------------------
//VT-d register structure definitions

/*//VTD_VER_REG (sec. 10.4.1)
typedef union {
  u32 value;
  struct
  {
    u32 min : 4;			//minor version no.
    u32 max : 4;			//major version no.
    u32 rsvdz : 24;		//reserved
  } __attribute__((packed)) bits;
} __attribute__ ((packed)) VTD_VER_REG;
*/

//VTD_CAP_REG (sec. 10.4.2)
typedef struct {
    u32 nd      ;//: 3;    		//no. of domains
    u32 afl     ;//: 1;			//advanced fault logging
    u32 rwbf    ;//: 1;			//required write-buffer flushing
    u32 plmr    ;//: 1;			//protected low-memory region
    u32 phmr    ;//: 1;			//protected high-memory region
    u32 cm      ;//: 1;				//caching mode
    u32 sagaw   ;//: 5;			//supported adjuested guest address widths
    u32 rsvdz0  ;//: 3;		//reserved
    u32 mgaw    ;//: 6;			//maximum guest address width
    u32 zlr     ;//: 1;				//zero length read
    u32 isoch   ;//: 1;			//isochrony
    u32 fro     ;//: 10;			//fault-recording register offset
    u32 sps     ;//: 4;			//super-page support
    u32 rsvdz1  ;//: 1;		//reserved
    u32 psi     ;//: 1;				//page selective invalidation
    u32 nfr     ;//: 8;				//no. of fault-recording registers
    u32 mamv    ;//: 6;			//max. address mask value
    u32 dwd     ;//: 1;				//DMA write draining
    u32 drd     ;//: 1;				//DMA read draining
    u32 rsvdz2  ;//: 8;		//reserved
} __attribute__ ((packed)) VTD_CAP_REG;


#define pack_VTD_CAP_REG(s) \
    (u64)( \
    (((u64)(s)->rsvdz2 &   0x00000000000000FFULL) << 56) | \
    (((u64)(s)->drd    &   0x0000000000000001ULL) << 55) | \
    (((u64)(s)->dwd    &   0x0000000000000001ULL) << 54) | \
    (((u64)(s)->mamv   &   0x000000000000003FULL) << 48) | \
    (((u64)(s)->nfr    &   0x00000000000000FFULL) << 40) | \
    (((u64)(s)->psi    &   0x0000000000000001ULL) << 39) | \
    (((u64)(s)->rsvdz1 &   0x0000000000000001ULL) << 38) | \
    (((u64)(s)->sps    &   0x000000000000000FULL) << 34) | \
    (((u64)(s)->fro    &   0x00000000000003FFULL) << 24) | \
    (((u64)(s)->isoch  &   0x0000000000000001ULL) << 23) | \
    (((u64)(s)->zlr    &   0x0000000000000001ULL) << 22) | \
    (((u64)(s)->mgaw   &   0x000000000000003FULL) << 16) | \
    (((u64)(s)->rsvdz0 &   0x0000000000000007ULL) << 13) | \
    (((u64)(s)->sagaw  &   0x000000000000001FULL) << 8 ) | \
    (((u64)(s)->cm     &   0x0000000000000001ULL) << 7 ) | \
    (((u64)(s)->phmr   &   0x0000000000000001ULL) << 6 ) | \
    (((u64)(s)->plmr   &   0x0000000000000001ULL) << 5 ) | \
    (((u64)(s)->rwbf   &   0x0000000000000001ULL) << 4 ) | \
    (((u64)(s)->afl    &   0x0000000000000001ULL) << 3 ) | \
    (((u64)(s)->nd     &   0x0000000000000007ULL) << 0 )  \
    )

#define unpack_VTD_CAP_REG(s, value) \
    (s)->rsvdz2     = (u32)(((u64)value >>  56 ) & 0x00000000000000FFULL); \
    (s)->drd        = (u32)(((u64)value >>  55 ) & 0x0000000000000001ULL); \
    (s)->dwd        = (u32)(((u64)value >>  54 ) & 0x0000000000000001ULL); \
    (s)->mamv       = (u32)(((u64)value >>  48 ) & 0x000000000000003FULL); \
    (s)->nfr        = (u32)(((u64)value >>  40 ) & 0x00000000000000FFULL); \
    (s)->psi        = (u32)(((u64)value >>  39 ) & 0x0000000000000001ULL); \
    (s)->rsvdz1     = (u32)(((u64)value >>  38 ) & 0x0000000000000001ULL); \
    (s)->sps        = (u32)(((u64)value >>  34 ) & 0x000000000000000FULL); \
    (s)->fro        = (u32)(((u64)value >>  24 ) & 0x00000000000003FFULL); \
    (s)->isoch      = (u32)(((u64)value >>  23 ) & 0x0000000000000001ULL); \
    (s)->zlr        = (u32)(((u64)value >>  22 ) & 0x0000000000000001ULL); \
    (s)->mgaw       = (u32)(((u64)value >>  16 ) & 0x000000000000003FULL); \
    (s)->rsvdz0     = (u32)(((u64)value >>  13 ) & 0x0000000000000007ULL); \
    (s)->sagaw      = (u32)(((u64)value >>  8  ) & 0x000000000000001FULL); \
    (s)->cm         = (u32)(((u64)value >>  7  ) & 0x0000000000000001ULL); \
    (s)->phmr       = (u32)(((u64)value >>  6  ) & 0x0000000000000001ULL); \
    (s)->plmr       = (u32)(((u64)value >>  5  ) & 0x0000000000000001ULL); \
    (s)->rwbf       = (u32)(((u64)value >>  4  ) & 0x0000000000000001ULL); \
    (s)->afl        = (u32)(((u64)value >>  3  ) & 0x0000000000000001ULL); \
    (s)->nd         = (u32)(((u64)value >>  0  ) & 0x0000000000000007ULL);



//VTD_ECAP_REG (sec. 10.4.3)
typedef struct {
    u32 c       ;//:1;					//coherency
    u32 qi      ;//:1;					//queued invalidation support
    u32 di      ;//:1;					//device IOTLB support
    u32 ir      ;//:1;					//interrupt remapping support
    u32 eim     ;//:1;				//extended interrupt mode
    u32 ch      ;//:1;					//caching hints
    u32 pt      ;//:1;					//pass through
    u32 sc      ;//:1;					//snoop control
    u32 iro     ;//:10;				//IOTLB register offset
    u32 rsvdz0  ;//: 2;		//reserved
    u32 mhmv    ;//: 4;			//maximum handle mask value
    u32 rsvdz1  ;//: 32;		//reserved
    u32 rsvdz2  ;//: 8;		//reserved
} __attribute__ ((packed)) VTD_ECAP_REG;

#define pack_VTD_ECAP_REG(s) \
    (u64)( \
    (((u64)(s)->rsvdz2 &   0x00000000000000FFULL) << 56) | \
    (((u64)(s)->rsvdz1 &   0x00000000FFFFFFFFULL) << 24) | \
    (((u64)(s)->mhmv   &   0x000000000000000FULL) << 20) | \
    (((u64)(s)->rsvdz0 &   0x0000000000000003ULL) << 18) | \
    (((u64)(s)->iro    &   0x00000000000003FFULL) << 8 ) | \
    (((u64)(s)->sc     &   0x0000000000000001ULL) << 7 ) | \
    (((u64)(s)->pt     &   0x0000000000000001ULL) << 6 ) | \
    (((u64)(s)->ch     &   0x0000000000000001ULL) << 5 ) | \
    (((u64)(s)->eim    &   0x0000000000000001ULL) << 4 ) | \
    (((u64)(s)->ir     &   0x0000000000000001ULL) << 3 ) | \
    (((u64)(s)->di     &   0x0000000000000001ULL) << 2 ) | \
    (((u64)(s)->qi     &   0x0000000000000001ULL) << 1 ) | \
    (((u64)(s)->c      &   0x0000000000000001ULL) << 0 )  \
    )

#define unpack_VTD_ECAP_REG(s, value) \
    (s)->rsvdz2     = (u32)(((u64)value >>  56 ) & 0x00000000000000FFULL); \
    (s)->rsvdz1     = (u32)(((u64)value >>  24 ) & 0x00000000FFFFFFFFULL); \
    (s)->mhmv       = (u32)(((u64)value >>  20 ) & 0x000000000000000FULL); \
    (s)->rsvdz0     = (u32)(((u64)value >>  18 ) & 0x0000000000000003ULL); \
    (s)->iro        = (u32)(((u64)value >>  8  ) & 0x00000000000003FFULL); \
    (s)->sc         = (u32)(((u64)value >>  7  ) & 0x0000000000000001ULL); \
    (s)->pt         = (u32)(((u64)value >>  6  ) & 0x0000000000000001ULL); \
    (s)->ch         = (u32)(((u64)value >>  5  ) & 0x0000000000000001ULL); \
    (s)->eim        = (u32)(((u64)value >>  4  ) & 0x0000000000000001ULL); \
    (s)->ir         = (u32)(((u64)value >>  3  ) & 0x0000000000000001ULL); \
    (s)->di         = (u32)(((u64)value >>  2  ) & 0x0000000000000001ULL); \
    (s)->qi         = (u32)(((u64)value >>  1  ) & 0x0000000000000001ULL); \
    (s)->c          = (u32)(((u64)value >>  0  ) & 0x0000000000000001ULL);




//VTD_GCMD_REG (sec. 10.4.4)
typedef struct {
    u32 rsvdz0  ;//: 23;		//reserved
    u32 cfi     ;//: 1;				//compatibility format interrupt
    u32 sirtp   ;//: 1;			//set interrupt remap table pointer
    u32 ire     ;//:1;				//interrupt remapping enable
    u32 qie     ;//:1;				//queued invalidation enable
    u32 wbf     ;//:1;				//write buffer flush
    u32 eafl    ;//:1;				//enable advanced fault logging
    u32 sfl     ;//:1;				//set fault log
    u32 srtp    ;//:1;				//set root table pointer
    u32 te      ;//:1;					//translation enable
} __attribute__ ((packed)) VTD_GCMD_REG;

#define pack_VTD_GCMD_REG(s) \
    (u32)( \
    (((u32)(s)->te       & 0x00000001UL) << 31) | \
    (((u32)(s)->srtp     & 0x00000001UL) << 30) | \
    (((u32)(s)->sfl      & 0x00000001UL) << 29) | \
    (((u32)(s)->eafl     & 0x00000001UL) << 28) | \
    (((u32)(s)->wbf      & 0x00000001UL) << 27) | \
    (((u32)(s)->qie      & 0x00000001UL) << 26) | \
    (((u32)(s)->ire      & 0x00000001UL) << 25) | \
    (((u32)(s)->sirtp    & 0x00000001UL) << 24) | \
    (((u32)(s)->cfi      & 0x00000001UL) << 23) | \
    (((u32)(s)->rsvdz0   & 0x007FFFFFUL) << 0 ) \
    )

#define unpack_VTD_GCMD_REG(s, value) \
    (s)->te         = (u32)(((u32)value >> 31) & 0x00000001UL); \
    (s)->srtp       = (u32)(((u32)value >> 30) & 0x00000001UL); \
    (s)->sfl        = (u32)(((u32)value >> 29) & 0x00000001UL); \
    (s)->eafl       = (u32)(((u32)value >> 28) & 0x00000001UL); \
    (s)->wbf        = (u32)(((u32)value >> 27) & 0x00000001UL); \
    (s)->qie        = (u32)(((u32)value >> 26) & 0x00000001UL); \
    (s)->ire        = (u32)(((u32)value >> 25) & 0x00000001UL); \
    (s)->sirtp      = (u32)(((u32)value >> 24) & 0x00000001UL); \
    (s)->cfi        = (u32)(((u32)value >> 23) & 0x00000001UL); \
    (s)->rsvdz0     = (u32)(((u32)value >> 0 ) & 0x007FFFFFUL);




//VTD_GSTS_REG (sec. 10.4.5)
typedef struct {
    u32 rsvdz0  ; //: 23;		//reserved
    u32 cfis    ; //:1;				//compatibility interrupt format status
    u32 irtps   ; //:1;			//interrupt remapping table pointer status
    u32 ires    ; //:1;				//interrupt remapping enable status
    u32 qies    ; //:1;				//queued invalidation enable status
    u32 wbfs    ; //:1;				//write buffer flush status
    u32 afls    ; //:1;				//advanced fault logging status
    u32 fls     ; //:1;				//fault log status
    u32 rtps    ; //:1;				//root table pointer status
    u32 tes     ; //:1;				//translation enable status
} __attribute__ ((packed)) VTD_GSTS_REG;

#define pack_VTD_GSTS_REG(s) \
    (u32)( \
    (((u32)(s)->tes      & 0x00000001UL) << 31) | \
    (((u32)(s)->rtps     & 0x00000001UL) << 30) | \
    (((u32)(s)->fls      & 0x00000001UL) << 29) | \
    (((u32)(s)->afls     & 0x00000001UL) << 28) | \
    (((u32)(s)->wbfs     & 0x00000001UL) << 27) | \
    (((u32)(s)->qies     & 0x00000001UL) << 26) | \
    (((u32)(s)->ires     & 0x00000001UL) << 25) | \
    (((u32)(s)->irtps    & 0x00000001UL) << 24) | \
    (((u32)(s)->cfis     & 0x00000001UL) << 23) | \
    (((u32)(s)->rsvdz0   & 0x007FFFFFUL) << 0 ) \
    )

#define unpack_VTD_GSTS_REG(s, value) \
     (s)->tes       = (u32)(((u32)value >> 31) & 0x00000001UL); \
     (s)->rtps      = (u32)(((u32)value >> 30) & 0x00000001UL); \
     (s)->fls       = (u32)(((u32)value >> 29) & 0x00000001UL); \
     (s)->afls      = (u32)(((u32)value >> 28) & 0x00000001UL); \
     (s)->wbfs      = (u32)(((u32)value >> 27) & 0x00000001UL); \
     (s)->qies      = (u32)(((u32)value >> 26) & 0x00000001UL); \
     (s)->ires      = (u32)(((u32)value >> 25) & 0x00000001UL); \
     (s)->irtps     = (u32)(((u32)value >> 24) & 0x00000001UL); \
     (s)->cfis      = (u32)(((u32)value >> 23) & 0x00000001UL); \
     (s)->rsvdz0    = (u32)(((u32)value >> 0 ) & 0x007FFFFFUL);



//VTD_RTADDR_REG (sec. 10.4.6)
typedef struct {
    u32 rsvdz0  ; //: 12;		//reserved
    u32 rta     ; //: 32;			//root table address
    u32 rta_high ; // : 22;			//root table address
} __attribute__ ((packed)) VTD_RTADDR_REG;

#define pack_VTD_RTADDR_REG(s) \
    (u64)( \
    (((u64)(s)->rta_high &   0x00000000003FFFFFULL) << 44) | \
    (((u64)(s)->rta      &   0x00000000FFFFFFFFULL) << 12) | \
    (((u64)(s)->rsvdz0   &   0x0000000000000FFFULL) << 0 )  \
    )

#define unpack_VTD_RTADDR_REG(s, value) \
    (s)->rta_high    = (u32)(((u64)value >>  44 ) & 0x00000000003FFFFFULL); \
    (s)->rta         = (u32)(((u64)value >>  12 ) & 0x00000000FFFFFFFFULL); \
    (s)->rsvdz0      = (u32)(((u64)value >>  0  ) & 0x0000000000000FFFULL);




//VTD_CCMD_REG (sec. 10.4.7)
typedef struct {
    u32 did     ; //:16;				//domain id
    u32 sid     ; //:16;				//source id
    u32 fm      ; //:2;					//function mask
    u32 rsvdz0  ; //: 25;		//reserved
    u32 caig    ; //:2;				//context invalidation actual granularity
    u32 cirg    ; //:2;				//context invalidation request granularity
    u32 icc     ; //:1;				//invalidate context-cache
} __attribute__ ((packed)) VTD_CCMD_REG;

#define pack_VTD_CCMD_REG(s) \
    (u64)( \
    (((u64)(s)->icc    &   0x0000000000000001ULL) << 63) | \
    (((u64)(s)->cirg   &   0x0000000000000003ULL) << 61) | \
    (((u64)(s)->caig   &   0x0000000000000003ULL) << 59) | \
    (((u64)(s)->rsvdz0 &   0x0000000001FFFFFFULL) << 34) | \
    (((u64)(s)->fm     &   0x0000000000000003ULL) << 32) | \
    (((u64)(s)->sid    &   0x000000000000FFFFULL) << 16) | \
    (((u64)(s)->did    &   0x000000000000FFFFULL) << 0 )  \
    )

#define unpack_VTD_CCMD_REG(s, value) \
    (s)->icc     = (u32)(((u64)value >>   63) & 0x0000000000000001ULL); \
    (s)->cirg    = (u32)(((u64)value >>   61) & 0x0000000000000003ULL); \
    (s)->caig    = (u32)(((u64)value >>   59) & 0x0000000000000003ULL); \
    (s)->rsvdz0  = (u32)(((u64)value >>   34) & 0x0000000001FFFFFFULL); \
    (s)->fm      = (u32)(((u64)value >>   32) & 0x0000000000000003ULL); \
    (s)->sid     = (u32)(((u64)value >>   16) & 0x000000000000FFFFULL); \
    (s)->did     = (u32)(((u64)value >>   0 ) & 0x000000000000FFFFULL);




//VTD_IOTLB_REG (sec. 10.4.8.1)

typedef struct {
    u32 rsvdz0  ; //: 32;		//reserved
    u32 did     ; //:16;				//domain-id
    u32 dw      ; //: 1;				//drain writes
    u32 dr      ; //:1;					//drain reads
    u32 rsvdz1  ; //: 7;		//reserved
    u32 iaig    ; //: 3;			//IOTLB actual invalidation granularity
    u32 iirg    ; //: 3;			//IOTLB request invalidation granularity
    u32 ivt     ; //: 1;				//invalidate IOTLB
} __attribute__ ((packed)) VTD_IOTLB_REG;

#define pack_VTD_IOTLB_REG(s) \
    (u64)( \
    (((u64)(s)->ivt &    0x0000000000000001ULL) << 63) | \
    (((u64)(s)->iirg &   0x0000000000000007ULL) << 60) | \
    (((u64)(s)->iaig &   0x0000000000000007ULL) << 57) | \
    (((u64)(s)->rsvdz1 & 0x000000000000007FULL) << 50) | \
    (((u64)(s)->dr &     0x0000000000000001ULL) << 49) | \
    (((u64)(s)->dw &     0x0000000000000001ULL) << 48) | \
    (((u64)(s)->did &    0x000000000000FFFFULL) << 32) | \
    (((u64)(s)->rsvdz0 & 0x00000000FFFFFFFFULL) << 0 ) \
    )

#define unpack_VTD_IOTLB_REG(s, value) \
    (s)->ivt = (u32)(((u64)value >>    63) & 0x0000000000000001ULL); \
    (s)->iirg = (u32)(((u64)value >>   60) & 0x0000000000000007ULL); \
    (s)->iaig = (u32)(((u64)value >>   57) & 0x0000000000000007ULL); \
    (s)->rsvdz1 = (u32)(((u64)value >> 50) & 0x000000000000007FULL); \
    (s)->dr = (u32)(((u64)value >>     49) & 0x0000000000000001ULL); \
    (s)->dw = (u32)(((u64)value >>     48) & 0x0000000000000001ULL); \
    (s)->did = (u32)(((u64)value >>    32) & 0x000000000000FFFFULL); \
    (s)->rsvdz0 = (u32)(((u64)value >> 0 ) & 0x00000000FFFFFFFFULL);


/*//VTD_IVA_REG (sec. 10.4.8.2)
typedef union {
  u64 value;
  struct
  {
    u32 am: 6;				//address mask
    u32 ih:1;					//invalidation hint
    u32 rsvdz0: 5;		//reserved
    u32 addr:32;			//address
    u32 addr_high :20;			//address
  } __attribute__((packed)) bits;
} __attribute__ ((packed)) VTD_IVA_REG;
*/

/*
//VTD_FSTS_REG	(sec. 10.4.9)
typedef union {
  u32 value;
  struct
  {
    u32 pfo:1;				//fault overflow
    u32 ppf:1;				//primary pending fault
    u32 afo:1;				//advanced fault overflow
    u32 apf:1;				//advanced pending fault
    u32 iqe:1;				//invalidation queue error
    u32 ice:1;				//invalidation completion error
    u32 ite:1;				//invalidation time-out error
    u32 rsvdz0: 1;		//reserved
    u32 fri:8;				//fault record index
    u32 rsvdz1: 16;		//reserved
  } __attribute__((packed)) bits;
} __attribute__ ((packed)) VTD_FSTS_REG;
*/


//VTD_FECTL_REG	(sec. 10.4.10)
typedef struct {
    u32 rsvdp0  ; //:30;		//reserved
    u32 ip      ; //:1;					//interrupt pending
    u32 im      ; //:1;					//interrupt mask
} __attribute__ ((packed)) VTD_FECTL_REG;

#define pack_VTD_FECTL_REG(s) \
    (u32)( \
    (((u32)(s)->im & 0x00000001UL) << 31) | \
    (((u32)(s)->ip & 0x00000001UL) << 30) | \
    (((u32)(s)->rsvdp0 & 0x3FFFFFFFUL) << 0) \
    )

#define unpack_VTD_FECTL_REG(s, value) \
    (s)->im = (u32)(((u32)value >> 31) & 0x00000001UL); \
    (s)->ip = (u32)(((u32)value >> 30) & 0x00000001UL); \
    (s)->rsvdp0 = (u32)(((u32)value >> 0) & 0x3FFFFFFFUL);


//VTD_PMEN_REG (sec. 10.4.16)
typedef struct {
    u32 prs     ; // :1;			//protected region status
    u32 rsvdp   ; //:30;		//reserved
    u32 epm     ; //:1;			//enable protected memory
} __attribute__ ((packed)) VTD_PMEN_REG;

#define pack_VTD_PMEN_REG(s) \
    (u32)( \
    (((u32)(s)->epm & 0x00000001UL) << 31) | \
    (((u32)(s)->rsvdp & 0x3FFFFFFFUL) << 1) | \
    (((u32)(s)->prs & 0x00000001UL) << 0) \
    )

#define unpack_VTD_PMEN_REG(s, value) \
    (s)->epm = (u32)(((u32)value >> 31) & 0x00000001UL); \
    (s)->rsvdp = (u32)(((u32)value >> 1) & 0x3FFFFFFFUL); \
    (s)->prs = (u32)(((u32)value >> 0) & 0x00000001UL);



//VTD_PLMBASE_REG (sec. 10.4.17)
typedef struct {
  u32 value;
} __attribute__ ((packed)) VTD_PLMBASE_REG;

//VTD_PLMLIMIT_REG (sec. 10.4.18)
typedef struct {
  u32 value;
} __attribute__ ((packed)) VTD_PLMLIMIT_REG;

//VTD_PHMBASE_REG (sec. 10.4.19)
typedef struct {
  u64 value;
} __attribute__ ((packed)) VTD_PHMBASE_REG;

//VTD_PHMLIMIT_REG (sec. 10.4.20)
typedef struct {
  u64 value;
} __attribute__ ((packed)) VTD_PHMLIMIT_REG;





#endif //__ASSEMBLY__

#endif //__XMHFHWM_VTD_H___
