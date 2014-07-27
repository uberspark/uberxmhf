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

// Advanced Configuration and Power-management Interface (ACPI) definitions
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __ACPI_H__
#define __ACPI_H__

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

#endif //__ACPI_H__
