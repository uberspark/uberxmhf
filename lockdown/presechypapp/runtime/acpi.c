#include <types.h>
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <error.h>
#include "acpi.h"


//------------------------------------------------------------------------------
//ACPI registers (as per v3.0b spec)
//the variables here are for internal use for this module only, they are
//initialized once and then mapped via defines in acpi.h 
//e.g PM1a_STS maps to __PM1a_STS
//we need to do this since the register addresses and sizes are not 
//constant and need to be computed at runtime
//sizes are in bytes
//currently we only support these registers to be I/O mapped, which is 
//usually the case for most ACPI chipsets

//PM1 event registers
u64 __PM1a_STS, __PM1a_EN, __PM1b_STS, __PM1b_EN;
u32 __PM1a_STS_size, __PM1a_EN_size, __PM1b_STS_size, __PM1b_EN_size;
//PM1 control registers
u64 __PM1_CNTa, __PM1_CNTb;
u32 __PM1_CNTa_size, __PM1_CNTb_size;
//PM2 control registers
u64 __PM2_CNT;
u32 __PM2_CNT_size;
//PM timer register
u64 __PM_TMR;
u32 __PM_TMR_size;
//processor control registers
u64 __P_CNT, __P_LVL2, __P_LVL3;
u32 __P_CNT_size, __P_LVL2_size, __P_LVL3_size;
//general purpose event registers
u64 __GPE0_STS, __GPE0_EN, __GPE1_STS, __GPE1_EN;
u32 __GPE0_STS_size, __GPE0_EN_size, __GPE1_STS_size, __GPE1_EN_size;
//reset register
u32 __acpi_reset_reg;
u8 __acpi_reset_reg_val;

//------------------------------------------------------------------------------

//get ACPI register addresses from system
void ACPIInitializeRegisters(void){
	ACPI_RSDP *rsdp;
	ACPI_XSDT *xsdt;
	u32 n_xsdt_entries, i;
	u64 *xsdtentrylist;
	ACPI_FADT *fadt;
	u8 fadt_found=0;
	ACPI_GAS *gas;
	
	rsdp=(ACPI_RSDP *)ACPIGetRSDP();
	if(!rsdp){
		printf("\nSystem is not ACPI Compliant (RSDP unavailable!)");
		HALT();
	}
	
	printf("ACPI System (RSDP phys addr=0x%08X)", rsdp);

	xsdt=(ACPI_XSDT *)(u32)rsdp->xsdtaddress;
	printf("\nXSDT phys addr=0x%08X", xsdt);
  printf("\nLength of XSDT=0x%08X, XSDT header length=0x%08X", xsdt->length, sizeof(ACPI_XSDT));
  
	n_xsdt_entries=(u32)((xsdt->length-sizeof(ACPI_XSDT))/8);
  printf("\nNumber of XSDT entries=%u", n_xsdt_entries);
  xsdtentrylist=(u64 *) ( (u32)xsdt + sizeof(ACPI_XSDT) );
  printf("\nxsdtentrylist phys addr=0x%08X", (u32)xsdtentrylist);
	
	for(i=0; i< n_xsdt_entries; i++){
    fadt=(ACPI_FADT *)( (u32)xsdtentrylist[i]);
    if(fadt->signature == ACPI_FADT_SIGNATURE){
    	fadt_found=1;
    	break;
    }
	}

	if(!fadt_found){
		printf("\nFADT not found!");
		HALT();
	}

	//get register addresses
	gas=(ACPI_GAS *)&fadt->x_pm2_cnt_blk;
	printf("\nPM2_CNT_BLK");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);
	
	gas=(ACPI_GAS *)&fadt->x_pm_tmr_blk;
	printf("\nPM_TMR_BLK");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);
	
	gas=(ACPI_GAS *)&fadt->x_gpe0_blk;
	printf("\nGPE0_BLK");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);
	gas=(ACPI_GAS *)&fadt->x_gpe1_blk;
	printf("\nGPE1_BLK");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);


	printf("\nPM1_EVT_LEN=0x%08X", fadt->pm1_evt_len);
	printf("\nPM1_CNT_LEN=0x%08X", fadt->pm1_cnt_len);
	printf("\nPM2_CNT_LEN=0x%08X", fadt->pm2_cnt_len);
	printf("\nPM_TMR_LEN=0x%08X", fadt->pm_tmr_len);
	printf("\nGPE0_BLK_LEN=0x%08X", fadt->gpe0_blk_len);
	printf("\nGPE1_BLK_LEN=0x%08X", fadt->gpe1_blk_len);
	
	
	//store register addresses
	gas=(ACPI_GAS *)&fadt->x_pm1a_evt_blk;
	printf("\nPM1a_EVT_BLK");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);
	__PM1a_STS=gas->address;
	__PM1a_STS_size=(gas->register_bit_width/8)/2;
	__PM1a_EN=gas->address+	((gas->register_bit_width/8)/2);
	__PM1a_EN_size=(gas->register_bit_width/8)/2;

	gas=(ACPI_GAS *)&fadt->x_pm1b_evt_blk;
	printf("\nPM1b_EVT_BLK");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);
	__PM1b_STS=gas->address;
	__PM1b_STS_size=(gas->register_bit_width/8)/2;
	__PM1b_EN=gas->address+	((gas->register_bit_width/8)/2);
	__PM1b_EN_size=(gas->register_bit_width/8)/2;

	gas=(ACPI_GAS *)&fadt->x_pm1a_cnt_blk;
	printf("\nPM1a_CNT_BLK");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);
	__PM1_CNTa=gas->address;
	__PM1_CNTa_size=fadt->pm1_cnt_len;

	gas=(ACPI_GAS *)&fadt->x_pm1b_cnt_blk;
	printf("\nPM1b_CNT_BLK");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);
	__PM1_CNTb=gas->address;
	__PM1_CNTb_size=fadt->pm1_cnt_len;
	
	//obtain ACPI reset register details
	//we ignore the RESET_REG_SUP bit when using ACPI reset mechanism
	//According to ACPI 3.0, FADT.flags.RESET_REG_SUP indicates
	//whether the ACPI reboot mechanism is supported.
	//However, some boxes have this bit clear, have a valid
	//ACPI_RESET_REG & RESET_VALUE
	//the following conditions must be met to indicate
	//that the reset register is supported.
	//1. Addr is not zero
	//2. RBW is eight
	//3. RBO is zero
	//4. ASID is 1
	gas=(ACPI_GAS *)&fadt->reset_reg;
	printf("\nRESET REG");
	printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
		gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
				gas->access_size, gas->address);
	printf("\nRESET VALUE=0x%02x", fadt->reset_value);
	ASSERT(gas->address && gas->address_space_id && (gas->register_bit_width == 8) &&
			(gas->register_bit_offset == 0) );
	__acpi_reset_reg = (u32)gas->address;
	__acpi_reset_reg_val = 	fadt->reset_value;		
			

	printf("\nPM1a_STS=0x%016X (size=%u bytes)", PM1a_STS, PM1a_STS_SIZE);
	printf("\nPM1a_EN=0x%016X (size=%u bytes)", PM1a_EN, PM1a_EN_SIZE);
	printf("\nPM1b_STS=0x%016X (size=%u bytes)", PM1b_STS, PM1b_STS_SIZE);
	printf("\nPM1b_EN=0x%016X (size=%u bytes)", PM1b_EN, PM1b_EN_SIZE);
	printf("\nPM1_CNTa=0x%016X (size=%u bytes)", PM1_CNTa, PM1_CNTa_SIZE);
	printf("\nPM1_CNTb=0x%016X (size=%u bytes)", PM1_CNTb, PM1_CNTb_SIZE);

	//what we need is PM1_CNTa and PM1a_STS register values
	//VTBOX - 804 and 800 respectively (16-bit access)

}

//------------------------------------------------------------------------------
u32 _ACPIGetRSDPComputeChecksum(u32 spaddr, u32 size){
  char *p;
  char checksum=0;
  u32 i;

  p=(char *)spaddr;
  
  for(i=0; i< size; i++)
    checksum+= (char)(*(p+i));
  
  return (u32)checksum;
}

//get the physical address of the root system description pointer (rsdp)
//return 0 if not found
u32 ACPIGetRSDP(void){
  u16 ebdaseg;
  u32 ebdaphys;
  u32 i, found=0;
  ACPI_RSDP *rsdp;
  
  //get EBDA segment from 040E:0000h in BIOS data area
  ebdaseg= * ((u16 *)0x0000040E);
  //convert it to its 32-bit physical address
  ebdaphys=(u32)(ebdaseg * 16);
  //search first 1KB of ebda for rsdp signature (8 bytes long)
  for(i=0; i < (1024-8); i+=16){
    rsdp=(ACPI_RSDP *)(ebdaphys+i);
    if(rsdp->signature == ACPI_RSDP_SIGNATURE){
      if(!_ACPIGetRSDPComputeChecksum((u32)rsdp, 20)){
        found=1;
        break;
      }
    }
  }
  
  if(found)
    return (u32)rsdp;
  
  //search within BIOS areas 0xE0000 to 0xFFFFF
  for(i=0xE0000; i < (0xFFFFF-8); i+=16){
    rsdp=(ACPI_RSDP *)i;
    if(rsdp->signature == ACPI_RSDP_SIGNATURE){
      if(!_ACPIGetRSDPComputeChecksum((u32)rsdp, 20)){
        found=1;
        break;
      }
    }
  }

  if(found)
    return (u32)rsdp;
  
  return 0;  
}
//------------------------------------------------------------------------------

//non-zero is success, else no ACPI
u32 ACPIIsSystemACPI(void){
	return(ACPIGetRSDP());
}