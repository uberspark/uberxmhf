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

// XMHF HWM sysmem BIOS areas
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHFHWM_BIOS_H__
#define __XMHFHWM_BIOS_H__

#define ACPI_RSDP_SIGNATURE  (0x2052545020445352ULL) //"RSD PTR "
#define ACPI_FADT_SIGNATURE  (0x50434146)  //"FACP"
#define ACPI_MADT_SIGNATURE	 (0x43495041)			//"APIC"

#define ACPI_GAS_ASID_SYSMEMORY		0x0
#define ACPI_GAS_ASID_SYSIO				0x1
#define ACPI_GAS_ASID_PCI					0x2
#define ACPI_GAS_ASID_EC					0x3
#define ACPI_GAS_ASID_SMBUS				0x4
#define ACPI_GAS_ASID_FFHW				0x7F

#define ACPI_GAS_ACCESS_UNDEF			0x0
#define ACPI_GAS_ACCESS_BYTE			0x1
#define ACPI_GAS_ACCESS_WORD			0x2
#define ACPI_GAS_ACCESS_DWORD			0x3
#define ACPI_GAS_ACCESS_QWORD			0x4

//maximum number of RSDT entries we support
#define	ACPI_MAX_RSDT_ENTRIES		(64)


#define XMHFHWM_BIOS_BDA_BASE			0x400
#define XMHFHWM_BIOS_BDA_SIZE			256

#define XMHFHWM_BIOS_EBDA_BASE			0x9ec00
#define XMHFHWM_BIOS_EBDA_SIZE			1100

#define XMHFHWM_BIOS_ROMBASE			0xE0000
#define XMHFHWM_BIOS_ROMSIZE                    0x20020

#define XMHFHWM_BIOS_ACPIRSDPBASE		0xE0000

#define XMHFHWM_BIOS_ACPIRSDTBASE		0xd87ef028UL
#define XMHFHWM_BIOS_ACPIRSDTENTRIESBASE	(XMHFHWM_BIOS_ACPIRSDTBASE + 0x24)
#define XMHFHWM_BIOS_VTDDMARTABLEBASE		0xd87feea8UL

#ifndef __ASSEMBLY__

//ACPI GAS, Generic Address Structure
typedef struct {
	u8 address_space_id;
	u8 register_bit_width;
	u8 register_bit_offset;
	u8 access_size;
	u64 address;
} __attribute__ ((packed)) ACPI_GAS;


//ACPI RSDP structure
typedef struct {
  u64 signature;
  u8 checksum;
  u8 oemid[6];
  u8 revision;
  u32 rsdtaddress;
  u32 length;
  u64 xsdtaddress;
  u8 xchecksum;
  u8 rsvd0[3];
} __attribute__ ((packed)) ACPI_RSDP;

//ACPI XSDT structure
typedef struct {
	u32 signature;
	u32 length;
	u8 revision;
	u8 checksum;
	u8 oemid[6];
	u64 oemtableid;
	u32 oemrevision;
	u32 creatorid;
	u32 creatorrevision;
} __attribute__ ((packed)) ACPI_XSDT;


//ACPI RSDT structure
typedef struct {
	u32 signature;
	u32 length;
	u8 revision;
	u8 checksum;
	u8 oemid[6];
	u64 oemtableid;
	u32 oemrevision;
	u32 creatorid;
	u32 creatorrevision;
} __attribute__ ((packed)) ACPI_RSDT;


/*
//ACPI RSDT structure for hwm
typedef struct {
	u32 signature;
	u32 length;
	u8 revision;
	u8 checksum;
	u8 oemid[6];
	u64 oemtableid;
	u32 oemrevision;
	u32 creatorid;
	u32 creatorrevision;
	u32 entries[ACPI_MAX_RSDT_ENTRIES];
} __attribute__ ((packed)) ACPI_RSDT_HWM;
*/



//ACPI MADT structure
typedef struct {
  u32 signature;
  u32 length;
  u8 revision;
  u8 checksum;
  u8 oemid[6];
  u64 oemtableid;
	u32 oemrevision;
	u32 creatorid;
	u32 creatorrevision;
	u32 lapicaddress;
	u32 mapicflags;
} __attribute__ ((packed)) ACPI_MADT;

//ACPI MADT APIC structure
typedef struct {
	u8 type;
	u8 length;
	u8 procid;
	u8 lapicid;
	u32 flags;
} __attribute__ ((packed)) ACPI_MADT_APIC;

//FADT structure
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
	u32 firmware_ctrl;
	u32 dsdt;
	u8 rsvd0;
	u8 preferred_pm_profile;
	u16 sci_int;
	u32 smi_cmd;
	u8 acpi_enable;
	u8 acpi_disable;
	u8 s4bios_req;
	u8 pstate_cnt;
	u32 pm1a_evt_blk;
	u32 pm1b_evt_blk;
	u32 pm1a_cnt_blk;
	u32 pm1b_cnt_blk;
	u32 pm2_cnt_blk;
	u32 pm_tmr_blk;
	u32 gpe0_blk;
	u32 gpe1_blk;
	u8 pm1_evt_len;
	u8 pm1_cnt_len;
	u8 pm2_cnt_len;
	u8 pm_tmr_len;
	u8 gpe0_blk_len;
	u8 gpe1_blk_len;
	u8 gpe1_base;
	u8 cst_cnt;
	u16 p_lvl2_lat;
	u16 p_lvl3_lat;
	u16 flushsize;
	u16 flushstride;
	u8 duty_offset;
	u8 duty_width;
	u8 day_alrm;
	u8 mon_alrm;
	u8 century;
	u16 iapc_boot_arch;
	u8 rsvd1;
	u32 flags;
	u8 reset_reg[12];
	u8 reset_value;
	u8 rsvd2[3];
	u64 x_firmware_ctrl;
	u64 x_dsdt;
	u8 x_pm1a_evt_blk[12];
	u8 x_pm1b_evt_blk[12];
	u8 x_pm1a_cnt_blk[12];
	u8 x_pm1b_cnt_blk[12];
	u8 x_pm2_cnt_blk[12];
	u8 x_pm_tmr_blk[12];
	u8 x_gpe0_blk[12];
	u8 x_gpe1_blk[12];
}__attribute__ ((packed)) ACPI_FADT;




#endif	//__ASSEMBLY__

//from _biosdata.h

#ifndef __ASSEMBLY__

//SMP configuration table signatures on x86 platforms
#define MPFP_SIGNATURE 					(0x5F504D5FUL) //"_MP_"
#define MPCONFTABLE_SIGNATURE 			(0x504D4350UL)  //"PCMP"

typedef struct {
  u32 signature;
  u32 paddrpointer;
  u8 length;
  u8 spec_rev;
  u8 checksum;
  u8 mpfeatureinfo1;
  u8 mpfeatureinfo2;
  u8 mpfeatureinfo3;
  u8 mpfeatureinfo4;
  u8 mpfeatureinfo5;
} __attribute__ ((packed)) MPFP;

typedef struct{
  u32 signature;
  u16 length;
  u8 spec_rev;
  u8 checksum;
  u8 oemid[8];
  u8 productid[12];
  u32 oemtableptr;
  u16 oemtablesize;
  u16 entrycount;
  u32 lapicaddr;
  u16 exttablelength;
  u16 exttablechecksum;
} __attribute__ ((packed)) MPCONFTABLE;

typedef struct {
  u8 entrytype;
  u8 lapicid;
  u8 lapicver;
  u8 cpuflags;
  u32 cpusig;
  u32 featureflags;
  u32 res0;
  u32 res1;
} __attribute__ ((packed)) MPENTRYCPU;


bool _impl_xmhfhwm_bios_read(u32 sysmemaddr, sysmem_read_t readsize, u64 *read_result);
bool _impl_xmhfhwm_bios_sysmemcopy(sysmem_copy_t sysmemcopy_type,
				u32 dstaddr, u32 srcaddr, u32 size);



#endif	//__ASSEMBLY__



#endif //__XMHFHWM_BIOS_H__
