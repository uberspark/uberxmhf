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

// vmx_eap.h - VMX VT-d (External Access Protection) declarations/definitions
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __VMX_EAP_H__
#define __VMX_EAP_H__

#define VTD_DMAR_SIGNATURE (0x52414D44) //"DMAR"
#define VTD_MAX_DRHD 8					// maximum number of DMAR h/w units

// VT-d register offsets (sec. 10.4, Intel_VT_for_Direct_IO)
#define VTD_VER_REG_OFF 0x000	 // arch. version (32-bit)
#define VTD_CAP_REG_OFF 0x008	 // h/w capabilities (64-bit)
#define VTD_ECAP_REG_OFF 0x010	 // h/w extended capabilities (64-bit)
#define VTD_GCMD_REG_OFF 0x018	 // global command (32-bit)
#define VTD_GSTS_REG_OFF 0x01C	 // global status (32-bit)
#define VTD_RTADDR_REG_OFF 0x020 // root-entry table address (64-bit)
#define VTD_CCMD_REG_OFF 0x028	 // manage context-entry cache (64-bit)
#define VTD_FSTS_REG_OFF 0x034	 // report fault/error status (32-bit)
#define VTD_FECTL_REG_OFF 0x038	 // interrupt control (32-bit)
#define VTD_PMEN_REG_OFF 0x064	 // enable DMA protected memory regions (32-bits)
#define VTD_IVA_REG_OFF 0x0DEAD	 // invalidate address register (64-bits)
								// note: the offset of this register is computed
// at runtime for a specified DMAR device
#define VTD_IOTLB_REG_OFF 0x0BEEF // IOTLB invalidate register (64-bits)
								  // note: the offset is VTD_IVA_REG_OFF + 8 and
								  // computed at runtime for a specified DMAR device

#define VTD_RTADDR_LEGACY_MODE (0UL << 10)	  // Enables legacy mode in the Root Table Address Register
#define VTD_RTADDR_SCALABLE_MODE (1UL << 10)  // Enables scalable mode in the Root Table Address Register
#define VTD_RTADDR_ABORT_DMA_MODE (3UL << 10) // Enables Abort-DMA mode in the Root Table Address Register

// GCMD_REG
#define VTD_GCMD_BIT_IRE	(25)
#define VTD_GCMD_BIT_QIE	(26)
#define VTD_GCMD_BIT_WBF	(27)
#define VTD_GCMD_BIT_EAFL	(28)
#define VTD_GCMD_BIT_SRTP	(30)
#define VTD_GCMD_BIT_TE		(31)

// FSTS_REG
#define VTD_FSTS_PFO (1 << 0) /* Primary Fault Overflow */
#define VTD_FSTS_PPF (1 << 1) /* Primary Pending Fault */
#define VTD_FSTS_IQE (1 << 4) /* Invalidation Queue Error */
#define VTD_FSTS_ICE (1 << 5) /* Invalidation Completion Error */
#define VTD_FSTS_ITE (1 << 6) /* Invalidation Time-out Error */
#define VTD_FSTS_PRO (1 << 7) /* Page Request Overflow */

// VT-d register access types (custom definitions)
#define VTD_REG_READ 0xaa  // read VTD register
#define VTD_REG_WRITE 0xbb // write VTD register

// Vt-d register access widths (custom definitions)
#define VTD_REG_32BITS 0x32ff
#define VTD_REG_64BITS 0x64ff

// Vt-d page-table bits
#define VTD_READ 0x1
#define VTD_WRITE 0x2
#define VTD_EXECUTE 0x4
#define VTD_SUPERPAGE (0x1UL << 7)
#define VTD_SNOOP (0x1UL << 11)

#define VTD_CAP_REG_FRO_MULTIPLIER (16UL) // If the register base address is X, and the value reported in this field
										  // is Y, the address for the first fault recording register is calculated as X+(16*Y).

#ifndef __ASSEMBLY__

//------------------------------------------------------------------------------
// VT-d register structure definitions

// VTD_VER_REG (sec. 10.4.1)
typedef union
{
	u32 value;
	struct
	{
		u32 min : 4,	// minor version no.
			max : 4,	// major version no.
			rsvdz : 24; // reserved
	} bits;
} __attribute__((packed)) VTD_VER_REG;

// VTD_CAP_REG (sec. 10.4.2)
typedef union
{
	u64 value;
	struct
	{
		u64 nd : 3,		// no. of domains
			afl : 1,	// advanced fault logging
			rwbf : 1,	// required write-buffer flushing
			plmr : 1,	// protected low-memory region
			phmr : 1,	// protected high-memory region
			cm : 1,		// caching mode
			sagaw : 5,	// supported adjuested guest address widths
			rsvdz0 : 3, // reserved
			mgaw : 6,	// maximum guest address width
			zlr : 1,	// zero length read
			isoch : 1,	// isochrony
			fro : 10,	// fault-recording register offset
			sps : 4,	// super-page support
			rsvdz1 : 1, // reserved
			psi : 1,	// page selective invalidation
			nfr : 8,	// no. of fault-recording registers
			mamv : 6,	// max. address mask value
			dwd : 1,	// DMA write draining
			drd : 1,	// DMA read draining
			rsvdz2 : 8; // reserved
	} bits;
} __attribute__((packed)) VTD_CAP_REG;

// VTD_ECAP_REG (sec. 10.4.3)
typedef union
{
	u64 value;
	struct
	{
		u64 c : 1,		 // coherency
			qi : 1,		 // queued invalidation support
			di : 1,		 // device IOTLB support
			ir : 1,		 // interrupt remapping support
			eim : 1,	 // extended interrupt mode
			ch : 1,		 // caching hints
			pt : 1,		 // pass through
			sc : 1,		 // snoop control
			iro : 10,	 // IOTLB register offset
			rsvdz0 : 2,	 // reserved
			mhmv : 4,	 // maximum handle mask value
			rsvdz1 : 40; // reserved
	} bits;
} __attribute__((packed)) VTD_ECAP_REG;

// VTD_GCMD_REG (sec. 10.4.4)
typedef union
{
	u32 value;
	struct
	{
		u32 rsvdz0 : 23, // reserved
			cfi : 1,	 // compatibility format interrupt
			sirtp : 1,	 // set interrupt remap table pointer
			ire : 1,	 // interrupt remapping enable
			qie : 1,	 // queued invalidation enable
			wbf : 1,	 // write buffer flush
			eafl : 1,	 // enable advanced fault logging
			sfl : 1,	 // set fault log
			srtp : 1,	 // set root table pointer
			te : 1;		 // translation enable
	} bits;
} __attribute__((packed)) VTD_GCMD_REG;

// VTD_GSTS_REG (sec. 10.4.5)
typedef union
{
	u32 value;
	struct
	{
		u32 rsvdz0 : 23, // reserved
			cfis : 1,	 // compatibility interrupt format status
			irtps : 1,	 // interrupt remapping table pointer status
			ires : 1,	 // interrupt remapping enable status
			qies : 1,	 // queued invalidation enable status
			wbfs : 1,	 // write buffer flush status
			afls : 1,	 // advanced fault logging status
			fls : 1,	 // fault log status
			rtps : 1,	 // root table pointer status
			tes : 1;	 // translation enable status
	} bits;
} __attribute__((packed)) VTD_GSTS_REG;

// VTD_RTADDR_REG (sec. 10.4.6)
typedef union
{
	u64 value;
	struct
	{
		u64 rsvdz0 : 12, // reserved
			rta : 52;	 // root table address
	} bits;
} __attribute__((packed)) VTD_RTADDR_REG;

// VTD_CCMD_REG (sec. 10.4.7)
typedef union
{
	u64 value;
	struct
	{
		u64 did : 16,	 // domain id
			sid : 16,	 // source id
			fm : 2,		 // function mask
			rsvdz0 : 25, // reserved
			caig : 2,	 // context invalidation actual granularity
			cirg : 2,	 // context invalidation request granularity
			icc : 1;	 // invalidate context-cache
	} bits;
} __attribute__((packed)) VTD_CCMD_REG;

// VTD_IOTLB_REG (sec. 10.4.8.1)
typedef union
{
	u64 value;
	struct
	{
		u64 rsvdz0 : 32, // reserved
			did : 16,	 // domain-id
			dw : 1,		 // drain writes
			dr : 1,		 // drain reads
			rsvdz1 : 7,	 // reserved
			iaig : 3,	 // IOTLB actual invalidation granularity
			iirg : 3,	 // IOTLB request invalidation granularity
			ivt : 1;	 // invalidate IOTLB
	} bits;
} __attribute__((packed)) VTD_IOTLB_REG;

// VTD_IVA_REG (sec. 10.4.8.2)
typedef union
{
	u64 value;
	struct
	{
		u64 am : 6,		// address mask
			ih : 1,		// invalidation hint
			rsvdz0 : 5, // reserved
			addr : 52;	// address
	} bits;
} __attribute__((packed)) VTD_IVA_REG;

// VTD_FSTS_REG	(sec. 10.4.9)
typedef union
{
	u32 value;
	struct
	{
		u32 pfo : 1,	 // fault overflow
			ppf : 1,	 // primary pending fault
			afo : 1,	 // advanced fault overflow
			apf : 1,	 // advanced pending fault
			iqe : 1,	 // invalidation queue error
			ice : 1,	 // invalidation completion error
			ite : 1,	 // invalidation time-out error
			pro : 1,	 // page request overflow
			fri : 8,	 // fault record index
			rsvdz1 : 16; // reserved
	} bits;
} __attribute__((packed)) VTD_FSTS_REG;

// VTD_FECTL_REG	(sec. 10.4.10)
typedef union
{
	u32 value;
	struct
	{
		u32 rsvdp0 : 30, // reserved
			ip : 1,		 // interrupt pending
			im : 1;		 // interrupt mask
	} bits;
} __attribute__((packed)) VTD_FECTL_REG;

// VTD_PMEN_REG (sec. 10.4.16)
typedef union
{
	u32 value;
	struct
	{
		u32 prs : 1,	// protected region status
			rsvdp : 30, // reserved
			epm : 1;	// enable protected memory
	} bits;
} __attribute__((packed)) VTD_PMEN_REG;

//------------------------------------------------------------------------------
// Vt-d DMAR structure
typedef struct
{
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
} __attribute__((packed)) VTD_DMAR;

typedef struct
{
	VTD_CAP_REG cap;
	VTD_ECAP_REG ecap;
} VTD_IOMMU_FLAGS;

// VT-d DRHD structure
typedef struct
{
	u16 type;
	u16 length;
	u8 flags;
	u8 rsvdz0;
	u16 pcisegment;
	u64 regbaseaddr;

	// Flags (not part of DRHD structure, but useful for DRHD programming)
	VTD_IOMMU_FLAGS iommu_flags;
} __attribute__((packed)) VTD_DRHD;

#define ACPI_DMAR_INCLUDE_ALL       (1)

#define vtd_cap_frr_mem_offset(drhd)	(uint32_t)(drhd->iommu_flags.cap.bits.fro * VTD_CAP_REG_FRO_MULTIPLIER)
#define vtd_cap_frr_nums(drhd)	(uint32_t)(drhd->iommu_flags.cap.bits.nfr + 1)
#define vtd_cap_require_wbf(drhd)	(drhd->iommu_flags.cap.bits.rwbf)
#define vtd_cap_plmr(drhd)	(drhd->iommu_flags.cap.bits.plmr)
#define vtd_cap_phmr(drhd)	(drhd->iommu_flags.cap.bits.phmr)

#define vtd_ecap_sc(drhd)	(drhd->iommu_flags.ecap.bits.sc)
#define vtd_ecap_c(drhd)	(drhd->iommu_flags.ecap.bits.c)

#endif //__ASSEMBLY__
#endif //__VMX_EAP_H__