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

//Intel VT-d declarations/definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __VTD_H__
#define __VTD_H__

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
#define VTD_READ						0x1
#define VTD_WRITE						0x2
#define VTD_SUPERPAGE				(0x1UL << 7)

//vt-d page table page walk lengths
#define VTD_PAGEWALK_3LEVEL     (0x3)
#define VTD_PAGEWALK_4LEVEL     (0x4)
#define VTD_PAGEWALK_NONE       (0x0)

#define VTD_RET_MAXPTRS         (256)
#define VTD_CET_MAXPTRS         (256)

#ifndef __ASSEMBLY__

//Vt-d DMAR structure
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

//VT-d DRHD structure
typedef struct{
  u16 type;
  u16 length;
  u8 flags;
  u8 rsvdz0;
  u16 pcisegment;
  u64 regbaseaddr;
}__attribute__ ((packed)) VTD_DRHD;

typedef u32 vtd_drhd_handle_t;


typedef union {
    u64 qwords[2];
    struct {
        u64 p : 1;
        u64 rsv0 : 11;
        u64 ctp : 52;
        u64 rsv1 : 64;
    }fields;
} __attribute__((packed)) vtd_ret_entry_t;

typedef union {
    u64 qwords[2];
    struct {
        u64 p : 1;
        u64 fpd : 1;
        u64 t : 2;
        u64 rsv0 : 8;
        u64 slptptr : 52;
        u64 aw : 3;
        u64 ign0 : 4;
        u64 rsv1 : 1;
        u64 did : 16;
        u64 rsv2 : 40;
    }fields;
} __attribute__((packed)) vtd_cet_entry_t;


typedef union {
    u64 entry;
    struct {
        u64 r : 1;
        u64 w : 1;
        u64 x : 1;
        u64 ign0 : 4;
        u64 rsv0 : 1;
        u64 ign1 : 3;
        u64 rsv1 : 1;
        u64 slpdpt : 40;
        u64 ign2 : 10;
        u64 rsv2 : 1;
        u64 ign3 : 1;
    }fields;
}__attribute__((packed)) vtd_pml4te_t;

typedef union {
    u64 entry;
    struct {
        u64 r : 1;
        u64 w : 1;
        u64 x : 1;
        u64 emt : 3;
        u64 pat : 1;
        u64 big : 1;
        u64 ign0 : 3;
        u64 snp : 1;
        u64 slpdt : 40;
        u64 ign1 : 10;
        u64 tm : 1;
        u64 ign2 : 1;
    }fields;
}__attribute__((packed)) vtd_pdpte_t;

typedef union {
    u64 entry;
    struct {
        u64 r : 1;
        u64 w : 1;
        u64 x : 1;
        u64 emt : 3;
        u64 pat : 1;
        u64 big : 1;
        u64 ign0 : 3;
        u64 snp : 1;
        u64 slpt : 40;
        u64 ign1 : 10;
        u64 tm : 1;
        u64 ign2 : 1;
    }fields;
}__attribute__((packed)) vtd_pdte_t;

typedef union {
    u64 entry;
    struct {
        u64 r : 1;
        u64 w : 1;
        u64 x : 1;
        u64 emt : 3;
        u64 pat : 1;
        u64 ign0 : 4;
        u64 snp : 1;
        u64 pageaddr : 40;
        u64 ign1 : 10;
        u64 tm : 1;
        u64 ign2 : 1;
    }fields;
}__attribute__((packed)) vtd_pte_t;

typedef struct {
    vtd_pml4te_t pml4t[PAE_MAXPTRS_PER_PML4T];
    vtd_pdpte_t pdpt[PAE_MAXPTRS_PER_PDPT];
    vtd_pdte_t pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
    vtd_pte_t pt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];
}__attribute__((packed)) vtd_slpgtbl_t;

typedef struct {
    u64 addr_vtd_pml4t;
    u64 addr_vtd_pdpt;
}__attribute__((packed)) vtd_slpgtbl_handle_t;

//------------------------------------------------------------------------------
//VT-d register structure definitions

//VTD_VER_REG (sec. 10.4.1)
typedef union {
  u32 value;
  struct
  {
    u32 min : 4;			//minor version no.
    u32 max : 4;			//major version no.
    u32 rsvdz : 24;		//reserved
  } bits;
} __attribute__ ((packed)) VTD_VER_REG;

//VTD_CAP_REG (sec. 10.4.2)
typedef union {
  u64 value;
  struct
  {
    u32 nd : 3;    		//no. of domains
    u32 afl : 1;			//advanced fault logging
    u32 rwbf : 1;			//required write-buffer flushing
    u32 plmr : 1;			//protected low-memory region
    u32 phmr : 1;			//protected high-memory region
    u32 cm : 1;				//caching mode
    u32 sagaw: 5;			//supported adjuested guest address widths
    u32 rsvdz0: 3;		//reserved
    u32 mgaw : 6;			//maximum guest address width
    u32 zlr: 1;				//zero length read
    u32 isoch: 1;			//isochrony
    u32 fro : 10;			//fault-recording register offset
    u32 sps : 4;			//super-page support
    u32 rsvdz1: 1;		//reserved
    u32 psi: 1;				//page selective invalidation
    u32 nfr: 8;				//no. of fault-recording registers
    u32 mamv: 6;			//max. address mask value
    u32 dwd: 1;				//DMA write draining
    u32 drd: 1;				//DMA read draining
    u32 rsvdz2: 8;		//reserved
  } bits;
} __attribute__ ((packed)) VTD_CAP_REG;

//VTD_ECAP_REG (sec. 10.4.3)
typedef union {
  u64 value;
  struct
  {
    u32 c:1;					//coherency
    u32 qi:1;					//queued invalidation support
    u32 di:1;					//device IOTLB support
    u32 ir:1;					//interrupt remapping support
    u32 eim:1;				//extended interrupt mode
    u32 ch:1;					//caching hints
    u32 pt:1;					//pass through
    u32 sc:1;					//snoop control
    u32 iro:10;				//IOTLB register offset
    u32 rsvdz0: 2;		//reserved
    u32 mhmv: 4;			//maximum handle mask value
    u64 rsvdz1: 40;		//reserved
  } bits;
} __attribute__ ((packed)) VTD_ECAP_REG;

//VTD_GCMD_REG (sec. 10.4.4)
typedef union {
  u32 value;
  struct
  {
    u32 rsvdz0: 23;		//reserved
    u32 cfi: 1;				//compatibility format interrupt
    u32 sirtp: 1;			//set interrupt remap table pointer
    u32 ire:1;				//interrupt remapping enable
    u32 qie:1;				//queued invalidation enable
    u32 wbf:1;				//write buffer flush
    u32 eafl:1;				//enable advanced fault logging
    u32 sfl:1;				//set fault log
    u32 srtp:1;				//set root table pointer
    u32 te:1;					//translation enable
  } bits;
} __attribute__ ((packed)) VTD_GCMD_REG;

//VTD_GSTS_REG (sec. 10.4.5)
typedef union {
  u32 value;
  struct
  {
    u32 rsvdz0: 23;		//reserved
    u32 cfis:1;				//compatibility interrupt format status
    u32 irtps:1;			//interrupt remapping table pointer status
    u32 ires:1;				//interrupt remapping enable status
    u32 qies:1;				//queued invalidation enable status
    u32 wbfs:1;				//write buffer flush status
    u32 afls:1;				//advanced fault logging status
    u32 fls:1;				//fault log status
    u32 rtps:1;				//root table pointer status
    u32 tes:1;				//translation enable status
  } bits;
} __attribute__ ((packed)) VTD_GSTS_REG;

//VTD_RTADDR_REG (sec. 10.4.6)
typedef union {
  u64 value;
  struct
  {
    u32 rsvdz0: 12;		//reserved
    u64 rta: 52;			//root table address
  } bits;
} __attribute__ ((packed)) VTD_RTADDR_REG;

//VTD_CCMD_REG (sec. 10.4.7)
typedef union {
  u64 value;
  struct
  {
    u32 did:16;				//domain id
    u32 sid:16;				//source id
    u32 fm:2;					//function mask
    u32 rsvdz0: 25;		//reserved
    u32 caig:2;				//context invalidation actual granularity
    u32 cirg:2;				//context invalidation request granularity
    u32 icc:1;				//invalidate context-cache
  } bits;
} __attribute__ ((packed)) VTD_CCMD_REG;

//VTD_IOTLB_REG (sec. 10.4.8.1)
typedef union {
  u64 value;
  struct
  {
    u32 rsvdz0: 32;		//reserved
    u32 did:16;				//domain-id
    u32 dw: 1;				//drain writes
    u32 dr:1;					//drain reads
    u32 rsvdz1: 7;		//reserved
    u32 iaig: 3;			//IOTLB actual invalidation granularity
    u32 iirg: 3;			//IOTLB request invalidation granularity
    u32 ivt: 1;				//invalidate IOTLB
  } bits;
} __attribute__ ((packed)) VTD_IOTLB_REG;

//VTD_IVA_REG (sec. 10.4.8.2)
typedef union {
  u64 value;
  struct
  {
    u32 am: 6;				//address mask
    u32 ih:1;					//invalidation hint
    u32 rsvdz0: 5;		//reserved
    u64 addr:52;			//address
  } bits;
} __attribute__ ((packed)) VTD_IVA_REG;


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
  } bits;
} __attribute__ ((packed)) VTD_FSTS_REG;

//VTD_FECTL_REG	(sec. 10.4.10)
typedef union {
  u32 value;
  struct
  {
    u32 rsvdp0:30;		//reserved
    u32 ip:1;					//interrupt pending
    u32 im:1;					//interrupt mask
  } bits;
} __attribute__ ((packed)) VTD_FECTL_REG;

//VTD_PMEN_REG (sec. 10.4.16)
typedef union {
  u32 value;
  struct
  {
    u32 prs:1;			//protected region status
    u32 rsvdp:30;		//reserved
    u32 epm:1;			//enable protected memory
  } bits;
} __attribute__ ((packed)) VTD_PMEN_REG;


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



/*bool xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(vtd_drhd_handle_t *maxhandle, u32 *dmar_phys_addr_var);
bool xmhfhw_platform_x86pc_vtd_drhd_initialize(vtd_drhd_handle_t drhd_handle);
bool xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(vtd_drhd_handle_t drhd_handle);
bool xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(vtd_drhd_handle_t drhd_handle, u64 ret_addr);
void xmhfhw_platform_x86pc_vtd_drhd_enable_translation(vtd_drhd_handle_t drhd_handle);
void xmhfhw_platform_x86pc_vtd_drhd_disable_translation(vtd_drhd_handle_t drhd_handle);
void xmhfhw_platform_x86pc_vtd_drhd_enable_pmr(vtd_drhd_handle_t drhd_handle);
void xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(vtd_drhd_handle_t drhd_handle);
void xmhfhw_platform_x86pc_vtd_drhd_set_plm_base_and_limit(vtd_drhd_handle_t drhd_handle, u32 base, u32 limit);
void xmhfhw_platform_x86pc_vtd_drhd_set_phm_base_and_limit(vtd_drhd_handle_t drhd_handle, u64 base, u64 limit);
u64 xmhfhw_platform_x86pc_vtd_drhd_reg_read(vtd_drhd_handle_t drhd_handle, u32 reg);
void xmhfhw_platform_x86pc_vtd_drhd_reg_write(vtd_drhd_handle_t drhd_handle, u32 reg, u64 value);
*/



//maximum number of RSDT entries we support
#define	ACPI_MAX_RSDT_ENTRIES		(256)

//==============================================================================
// local (static) variables and function definitions
//==============================================================================

//DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd=0;	//total number of DMAR h/w units
static bool vtd_drhd_scanned=false;	//set to true once DRHD units have been scanned in the system

//vt-d register access function
static inline void _vtd_reg(VTD_DRHD *dmardevice, u32 access, u32 reg, void *value){
  u32 regtype=VTD_REG_32BITS, regaddr=0;

	//obtain register type and base address
  switch(reg){
    //32-bit registers
    case  VTD_VER_REG_OFF:
    case  VTD_GCMD_REG_OFF:
    case  VTD_GSTS_REG_OFF:
    case  VTD_FSTS_REG_OFF:
    case  VTD_FECTL_REG_OFF:
    case  VTD_PMEN_REG_OFF:
    case  VTD_PLMBASE_REG_OFF:
    case  VTD_PLMLIMIT_REG_OFF:
      regtype=VTD_REG_32BITS;
      regaddr=dmardevice->regbaseaddr+reg;
      break;

    //64-bit registers
    case  VTD_CAP_REG_OFF:
    case  VTD_ECAP_REG_OFF:
    case  VTD_RTADDR_REG_OFF:
    case  VTD_CCMD_REG_OFF:
    case  VTD_PHMBASE_REG_OFF:
    case  VTD_PHMLIMIT_REG_OFF:
      regtype=VTD_REG_64BITS;
      regaddr=dmardevice->regbaseaddr+reg;
      break;

    case  VTD_IOTLB_REG_OFF:{
      VTD_ECAP_REG  t_vtd_ecap_reg;
      regtype=VTD_REG_64BITS;
      #ifndef __XMHF_VERIFICATION__
      _vtd_reg(dmardevice, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&t_vtd_ecap_reg.value);
      #endif
      regaddr=dmardevice->regbaseaddr+(t_vtd_ecap_reg.bits.iro*16)+0x8;
      break;
    }

    case  VTD_IVA_REG_OFF:{
      VTD_ECAP_REG  t_vtd_ecap_reg;
      regtype=VTD_REG_64BITS;
      #ifndef __XMHF_VERIFICATION__
      _vtd_reg(dmardevice, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&t_vtd_ecap_reg.value);
      #endif
      regaddr=dmardevice->regbaseaddr+(t_vtd_ecap_reg.bits.iro*16);
      break;
    }

    default:
      //_XDPRINTF_("\n%s: Halt, Unsupported register=%08x", __FUNCTION__, reg);
      HALT();
      break;
  }

  //perform the actual read or write request
	switch(regtype){
    case VTD_REG_32BITS:{	//32-bit r/w
      if(access == VTD_REG_READ)
        *((u32 *)value)= xmhfhw_sysmemaccess_readu32(regaddr);
      else
        xmhfhw_sysmemaccess_writeu32(regaddr, *((u32 *)value));

      break;
    }

    case VTD_REG_64BITS:{	//64-bit r/w
      if(access == VTD_REG_READ)
        *((u64 *)value)=xmhfhw_sysmemaccess_readu64(regaddr);
      else
        xmhfhw_sysmemaccess_writeu64(regaddr, *((u64 *)value));

      break;
    }

    default:
     //_XDPRINTF_("\n%s: Halt, Unsupported access width=%08x", __FUNCTION__, regtype);
     HALT();
  }

  return;
}


static inline VTD_DRHD *_vtd_get_drhd_struct(vtd_drhd_handle_t drhd_handle){
		VTD_DRHD *drhd = NULL;

		if(!vtd_drhd_scanned)
				return drhd;

		if(drhd_handle >= vtd_num_drhd)
			return drhd;

		return (VTD_DRHD *)&vtd_drhd[drhd_handle];

}

//scan for available DRHD units on the platform and populate the
//global variables set:
//vtd_drhd[] (struct representing a DRHD unit)
//vtd_num_drhd (number of DRHD units detected)
//vtd_dmar_table_physical_address (physical address of the DMAR table)
//returns: true if all is fine else false; dmar_phys_addr_var contains
//max. value of DRHD unit handle (0 through maxhandle-1 are valid handles
//that can subsequently be passed to any of the other vtd drhd functions)
//physical address of the DMAR table in the system
static inline bool xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(vtd_drhd_handle_t *maxhandle, u32 *dmar_phys_addr_var){
	ACPI_RSDP rsdp;
	ACPI_RSDT rsdt;
	u32 num_rsdtentries;
	u32 rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	u32 status;
	VTD_DMAR dmar;
	u32 i, dmarfound;
	u32 remappingstructuresaddrphys;
	u32 vtd_dmar_table_physical_address;

	//zero out rsdp and rsdt structures
	//memset(&rsdp, 0, sizeof(ACPI_RSDP));
	//memset(&rsdt, 0, sizeof(ACPI_RSDT));
	//sanity check NULL parameter
	if (dmar_phys_addr_var == NULL || maxhandle == NULL)
		return false;

	//set maxhandle to 0 to start with. if we have any errors before
	//we finalize maxhandle we can just bail out
	*maxhandle=0;

	//get ACPI RSDP
	status=xmhfhw_platform_x86pc_acpi_getRSDP(&rsdp);
	if(status == 0)
		return false;

	//_XDPRINTF_("\n%s: RSDP at %08x", __FUNCTION__, status);

	//grab ACPI RSDT
	xmhfhw_sysmemaccess_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	//_XDPRINTF_("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes",
	//	__FUNCTION__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));

	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	if(num_rsdtentries >= ACPI_MAX_RSDT_ENTRIES){
			//_XDPRINTF_("\n%s: Error num_rsdtentries(%u) > ACPI_MAX_RSDT_ENTRIES (%u)", __FUNCTION__, num_rsdtentries, ACPI_MAX_RSDT_ENTRIES);
			return false;
	}

	xmhfhw_sysmemaccess_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);
	//_XDPRINTF_("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
	//	(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);

	//find the VT-d DMAR table in the list (if any)
	for(i=0; i< num_rsdtentries; i++){
		xmhfhw_sysmemaccess_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));
		if(dmar.signature == VTD_DMAR_SIGNATURE){
		  dmarfound=1;
		  break;
		}
	}

	//if no DMAR table, bail out
	if(!dmarfound){
		//_XDPRINTF_("\n%s: Error No DMAR table", __FUNCTION__);
		return false;
	}

	vtd_dmar_table_physical_address = rsdtentries[i]; //DMAR table physical memory address;
	*dmar_phys_addr_var = vtd_dmar_table_physical_address; //store it in supplied argument
	//_XDPRINTF_("\n%s: DMAR at %08x", __FUNCTION__, vtd_dmar_table_physical_address);

	//detect DRHDs in the DMAR table
	i=0;
	remappingstructuresaddrphys=vtd_dmar_table_physical_address+sizeof(VTD_DMAR);
	//_XDPRINTF_("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);

	while(i < (dmar.length-sizeof(VTD_DMAR))){
		u16 type, length;
		xmhfhw_sysmemaccess_copy((u8 *)&type, (u8 *)(remappingstructuresaddrphys+i), sizeof(u16));
		xmhfhw_sysmemaccess_copy((u8 *)&length, (u8 *)(remappingstructuresaddrphys+i+sizeof(u16)), sizeof(u16));

		switch(type){
			case  0:  //DRHD
				//_XDPRINTF_("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructuresaddrphys+i), length);
				if(vtd_num_drhd >= VTD_MAX_DRHD){
						//_XDPRINTF_("\n%s: Error vtd_num_drhd (%u) > VTD_MAX_DRHD (%u)", __FUNCTION__, vtd_num_drhd, VTD_MAX_DRHD);
						return false;
				}
				xmhfhw_sysmemaccess_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructuresaddrphys+i), length);
				vtd_num_drhd++;
				i+=(u32)length;
				break;

			default:	//unknown type, we skip this
				i += (u32)length;
				break;
		}
	}
    //_XDPRINTF_("\n%s: total DRHDs detected= %u units", __FUNCTION__, vtd_num_drhd);

	//[DEBUG]: be a little verbose about what we found
	//_XDPRINTF_("\n%s: DMAR Devices:", __FUNCTION__);
	for(i=0; i < vtd_num_drhd; i++){
		VTD_CAP_REG cap;
		VTD_ECAP_REG ecap;
		//_XDPRINTF_("\n	Device %u on PCI seg %04x; base=0x%016llx", i,
		//			vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
		_vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
		//_XDPRINTF_("\n		cap=0x%016llx", (u64)cap.value);
		_vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
		//_XDPRINTF_("\n		ecap=0x%016llx", (u64)ecap.value);
	}

	*maxhandle = vtd_num_drhd;
	vtd_drhd_scanned = true;

	return true;
}

//initialize a given DRHD unit to meet our requirements
static inline bool xmhfhw_platform_x86pc_vtd_drhd_initialize(vtd_drhd_handle_t drhd_handle){
	VTD_GCMD_REG gcmd;
	VTD_GSTS_REG gsts;
	VTD_FECTL_REG fectl;
	VTD_CAP_REG cap;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if (drhd == NULL)
		return false;

	//verify required capabilities
	{
		//_XDPRINTF_("\nVerifying DRHD capabilities...");

		//read CAP register
		_vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);

		if(! (cap.bits.plmr && cap.bits.phmr) ){
			//_XDPRINTF_("\n%s: Error: PLMR unsupported", __FUNCTION__);
			return false;
		}

        if ( !((cap.bits.sagaw & 0x2) || (cap.bits.sagaw & 0x4)) ){
            //_XDPRINTF_("%s: Error: we only support 3-level or 4-level tables (%x)\n", __FUNCTION__, cap.bits.sagaw);
			return false;
        }

		//_XDPRINTF_("\nDRHD unit has all required capabilities");
	}

	//setup fault logging
	//_XDPRINTF_("\nSetting DRHD Fault-reporting to NON-INTERRUPT mode...");
	{
		//read FECTL
		  fectl.value=0;
		_vtd_reg(drhd, VTD_REG_READ, VTD_FECTL_REG_OFF, (void *)&fectl.value);

		//set interrupt mask bit and write
		fectl.bits.im=1;
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_FECTL_REG_OFF, (void *)&fectl.value);

		//check to see if the IM bit actually stuck
		_vtd_reg(drhd, VTD_REG_READ, VTD_FECTL_REG_OFF, (void *)&fectl.value);

		if(!fectl.bits.im){
		  //_XDPRINTF_("\n%s: Error: Failed to set fault-reporting.", __FUNCTION__);
		  return false;
		}
	}
	//_XDPRINTF_("\nDRHD Fault-reporting set to NON-INTERRUPT mode.");

	return true;
}


//invalidate DRHD caches
//note: we do global invalidation currently
//returns: true if all went well, else false
static inline bool xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(vtd_drhd_handle_t drhd_handle){
	VTD_CCMD_REG ccmd;
	VTD_IOTLB_REG iotlb;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if (drhd == NULL)
		return false;

	//invalidate CET cache
  	//wait for context cache invalidation request to send
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
    }while(ccmd.bits.icc);

	//initialize CCMD to perform a global invalidation
    ccmd.value=0;
    ccmd.bits.cirg=1; //global invalidation
    ccmd.bits.icc=1;  //invalidate context cache

    //perform the invalidation
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_CCMD_REG_OFF, (void *)&ccmd.value);

	//wait for context cache invalidation completion status
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
    }while(ccmd.bits.icc);

	//if all went well CCMD CAIG = CCMD CIRG (i.e., actual = requested invalidation granularity)
	if(ccmd.bits.caig != 0x1){
		//_XDPRINTF_("\n%s: Error: Invalidatation of CET failed (%u)", __FUNCTION__, ccmd.bits.caig);
		return false;
	}

	//invalidate IOTLB
    //initialize IOTLB to perform a global invalidation
	iotlb.value=0;
    iotlb.bits.iirg=1; //global invalidation
    iotlb.bits.ivt=1;	 //invalidate

    //perform the invalidation
	_vtd_reg(drhd, VTD_REG_WRITE, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);

    //wait for the invalidation to complete
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
    }while(iotlb.bits.ivt);

    //if all went well IOTLB IAIG = IOTLB IIRG (i.e., actual = requested invalidation granularity)
	if(iotlb.bits.iaig != 0x1){
		//_XDPRINTF_("\n%s: Error: Invalidation of IOTLB failed (%u)", __FUNCTION__, iotlb.bits.iaig);
		return false;
    }

	return true;
}


//VT-d translation has 1 root entry table (RET) of 4kb
//each root entry (RE) is 128-bits which gives us 256 entries in the
//RET, each corresponding to a PCI bus num. (0-255)
//each RE points to a context entry table (CET) of 4kb
//each context entry (CE) is 128-bits which gives us 256 entries in
//the CET, accounting for 32 devices with 8 functions each as per the
//PCI spec.
//each CE points to a PDPT type paging structure for  device
static inline bool xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(vtd_drhd_handle_t drhd_handle,  u64 ret_addr){
	VTD_RTADDR_REG rtaddr;
	VTD_GCMD_REG gcmd;
	VTD_GSTS_REG gsts;
	u32 retbuffer_paddr = hva2spa((u32)ret_addr);
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if (drhd == NULL)
		return false;

	//setup DRHD RET (root-entry)
	//_XDPRINTF_("\nSetting up DRHD RET...");
	{
		//setup RTADDR with base of RET
		rtaddr.value=(u64)retbuffer_paddr;
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_RTADDR_REG_OFF, (void *)&rtaddr.value);

		//latch RET address by using GCMD.SRTP
		gcmd.value=0;
		gcmd.bits.srtp=1;
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);

		//ensure the RET address was latched by the h/w
		_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);

		if(!gsts.bits.rtps){
			//_XDPRINTF_("\n%s: Error	Failed to latch RTADDR");
			return false;
		}
	}
	//_XDPRINTF_("\nDRHD RET initialized.");

	return true;
}


//enable VT-d translation
static inline void xmhfhw_platform_x86pc_vtd_drhd_enable_translation(vtd_drhd_handle_t drhd_handle){
	VTD_GCMD_REG gcmd;
	VTD_GSTS_REG gsts;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if (drhd == NULL)
		return;


	//turn on translation
	//_XDPRINTF_("\nEnabling VT-d translation...");
	{
		gcmd.value=0;
		gcmd.bits.te=1;
		#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
		assert(gcmd.bits.te == 1);
		#endif

		_vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);

		//wait for translation enabled status to go green...
		_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
		while(!gsts.bits.tes){
			_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
		}
	}
	//_XDPRINTF_("\nVT-d translation enabled.");

	return;
}

//disable VT-d translation
static inline void xmhfhw_platform_x86pc_vtd_drhd_disable_translation(vtd_drhd_handle_t drhd_handle){
	VTD_GCMD_REG gcmd;
	VTD_GSTS_REG gsts;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if ( drhd == NULL)
		return;

	//disable translation
	//_XDPRINTF_("\nDisabling VT-d translation...");
	{
		gcmd.value=0;
		gcmd.bits.te=0;

		_vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);

		//wait for translation enabled status to go red...
		_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
		while(gsts.bits.tes){
			_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
		}
	}
	//_XDPRINTF_("\nVT-d translation disabled.");

	return;
}

//enable protected memory region (PMR)
static inline void xmhfhw_platform_x86pc_vtd_drhd_enable_pmr(vtd_drhd_handle_t drhd_handle){
    VTD_PMEN_REG pmen;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if (drhd == NULL)
		return;

	//_XDPRINTF_("\nEnabling PMR...");
	{
		pmen.bits.epm=1;	//enable PMR
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_PMEN_REG_OFF, (void *)&pmen.value);

		//wait for PMR enabled...
		do{
			_vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
		}while(!pmen.bits.prs);
	}
	//_XDPRINTF_("\nDRHD PMR enabled.");

}

//disable protected memory region (PMR)
static inline void xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(vtd_drhd_handle_t drhd_handle){
    VTD_PMEN_REG pmen;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if(drhd == NULL)
		return;

	//_XDPRINTF_("\nDisabling PMR...");
	{
		pmen.bits.epm=0;	//disable PMR
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_PMEN_REG_OFF, (void *)&pmen.value);

		//wait for PMR disabled...
		do{
			_vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
		}while(pmen.bits.prs);
	}
	//_XDPRINTF_("\nDRHD PMR disabled.");

}

//set DRHD PLMBASE and PLMLIMIT PMRs
static inline void xmhfhw_platform_x86pc_vtd_drhd_set_plm_base_and_limit(vtd_drhd_handle_t drhd_handle, u32 base, u32 limit){
	VTD_PLMBASE_REG plmbase;
	VTD_PLMLIMIT_REG plmlimit;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if(drhd == NULL)
		return;

	//set PLMBASE register
	plmbase.value = base;
	_vtd_reg(drhd, VTD_REG_WRITE, VTD_PLMBASE_REG_OFF, (void *)&plmbase.value);

	//set PLMLIMIT register
	plmlimit.value = limit;
	_vtd_reg(drhd, VTD_REG_WRITE, VTD_PLMLIMIT_REG_OFF, (void *)&plmlimit.value);
}


//set DRHD PHMBASE and PHMLIMIT PMRs
static inline void xmhfhw_platform_x86pc_vtd_drhd_set_phm_base_and_limit(vtd_drhd_handle_t drhd_handle, u64 base, u64 limit){
	VTD_PHMBASE_REG phmbase;
	VTD_PHMLIMIT_REG phmlimit;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if (drhd == NULL)
		return;

	//set PHMBASE register
	phmbase.value = base;
	_vtd_reg(drhd, VTD_REG_WRITE, VTD_PHMBASE_REG_OFF, (void *)&phmbase.value);

	//set PLMLIMIT register
	phmlimit.value = limit;
	_vtd_reg(drhd, VTD_REG_WRITE, VTD_PHMLIMIT_REG_OFF, (void *)&phmlimit.value);
}

//read VT-d register
static inline u64 xmhfhw_platform_x86pc_vtd_drhd_reg_read(vtd_drhd_handle_t drhd_handle, u32 reg){
    u64 __regval=0;
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	_vtd_reg(drhd, VTD_REG_READ, reg, (void *)&__regval);

    return __regval;
}

//write VT-d register
static inline void xmhfhw_platform_x86pc_vtd_drhd_reg_write(vtd_drhd_handle_t drhd_handle, u32 reg, u64 value){
	VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	_vtd_reg(drhd, VTD_REG_WRITE, reg, (void *)&value);
}


#endif //__ASSEMBLY__

#endif //__VTD_H__
