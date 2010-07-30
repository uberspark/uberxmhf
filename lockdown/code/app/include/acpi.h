// Advanced Configuration and Power-management Interface (ACPI) definitions
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __ACPI_H__
#define __ACPI_H__

#define ACPI_RSDP_SIGNATURE  (0x2052545020445352ULL) //"RSD PTR " 
#define ACPI_FADT_SIGNATURE  (0x50434146)  //"FACP"

//#define ACPI_CONTROLREG_PORT					0x1004	//machine specific
//#define	ACPI_STATUSREG_PORT						0x1000

//VTBOX (supermicro)
//#define ACPI_CONTROLREG_PORT					0x804	//machine specific
//#define	ACPI_STATUSREG_PORT						0x800

//ADAMS (hp laptop)
//#define ACPI_CONTROLREG_PORT					0x404	//machine specific
//#define	ACPI_STATUSREG_PORT						0x400


extern u64 __PM1a_STS, __PM1a_EN, __PM1b_STS, __PM1b_EN;
extern u64 __PM1_CNTa, __PM1_CNTb;
extern u32 __PM1a_STS_size, __PM1a_EN_size, __PM1b_STS_size, __PM1b_EN_size;
extern u32 __PM1_CNTa_size, __PM1_CNTb_size;


#define PM1a_STS			__PM1a_STS
#define PM1a_STS_SIZE	__PM1a_STS_size
#define PM1a_EN				__PM1a_EN
#define PM1a_EN_SIZE	__PM1a_EN_size
#define PM1b_STS			__PM1b_STS
#define PM1b_STS_SIZE	__PM1b_STS_size
#define PM1b_EN				__PM1b_EN
#define PM1b_EN_SIZE	__PM1b_EN_size
#define PM1_CNTa			__PM1_CNTa
#define PM1_CNTa_SIZE	__PM1_CNTa_size
#define PM1_CNTb			__PM1_CNTb
#define PM1_CNTb_SIZE	__PM1_CNTb_size


u32 ACPIGetRSDP(void);
void ACPIInitializeRegisters(void);
u32 ACPIIsSystemACPI(void);

//ACPI GAS, Generic Address Structure
typedef struct {
	u8 address_space_id;
	u8 register_bit_width;
	u8 register_bit_offset;
	u8 access_size;
	u64 address;
} __attribute__ ((packed)) ACPI_GAS;

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


//ACPI RSDP structure
typedef struct {
  u64 signature;
  u8 checksum;
  u8 oemid[6];
  u8 revision;
  u32 rstdaddress;
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

#endif //__ACPI_H__