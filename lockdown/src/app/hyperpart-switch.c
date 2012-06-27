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

// ACPI interface implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>

#include <lockdown.h>


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
	ACPI_RSDP rsdp;
	u32 rsdp_paddr;
#if 0
	ACPI_XSDT *xsdt;
	u32 n_xsdt_entries
	u64 *xsdtentrylist;
	ACPI_GAS *gas;
#else
	//RSDT method
	ACPI_RSDT *rsdt;
	u32 n_rsdt_entries;
	u32 *rsdtentrylist;	
#endif
	u32 i;
	ACPI_FADT *fadt;
	u8 fadt_found=0;
	
	//rsdp=(ACPI_RSDP *)acpi_getRSDP();
	rsdp_paddr = emhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
	if(!rsdp_paddr){
		printf("\nSystem is not ACPI Compliant (RSDP unavailable!)");
		HALT();
	}
	
	printf("\nACPI System (RSDP phys addr=0x%08X)", rsdp_paddr);

#if 0
	xsdt=(ACPI_XSDT *)(u32)rsdp.xsdtaddress;
	printf("\nXSDT phys addr=0x%08X", (u32)xsdt);
  printf("\nLength of XSDT=0x%08X, XSDT header length=0x%08X", xsdt->length, sizeof(ACPI_XSDT));
  
	n_xsdt_entries=(u32)((xsdt->length-sizeof(ACPI_XSDT))/8);
  printf("\nNumber of XSDT entries=%u", n_xsdt_entries);
  xsdtentrylist=(u64 *) ( (u32)xsdt + sizeof(ACPI_XSDT) );
  //printf("\nxsdtentrylist phys addr=0x%08X", (u32)xsdtentrylist);
	
	for(i=0; i< n_xsdt_entries; i++){
    fadt=(ACPI_FADT *)( (u32)xsdtentrylist[i]);
    if(fadt->signature == ACPI_FADT_SIGNATURE){
    	fadt_found=1;
    	break;
    }
	}
#else
	//use standard RSDT method
	rsdt=(ACPI_RSDT *)(u32)rsdp.rsdtaddress;
	n_rsdt_entries=(u32)((rsdt->length-sizeof(ACPI_RSDT))/4);

	printf("\nACPI RSDT at 0x%08x", (u32)rsdt);
	printf("\n	len=0x%08x, headerlen=0x%08x, numentries=%u", 
			rsdt->length, sizeof(ACPI_RSDT), n_rsdt_entries);
  
	rsdtentrylist=(u32 *) ( (u32)rsdt + sizeof(ACPI_RSDT) );

	for(i=0; i< n_rsdt_entries; i++){
		fadt=(ACPI_FADT *)( (u32)rsdtentrylist[i]);
		if(fadt->signature == ACPI_FADT_SIGNATURE){
			fadt_found=1;
			break;
		}
	}	
#endif





	if(!fadt_found){
		printf("\nFADT not found!");
		HALT();
	}

#if 0
	//get register addresses
	gas=(ACPI_GAS *)&fadt->x_pm2_cnt_blk;
	//printf("\nPM2_CNT_BLK");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);
	
	gas=(ACPI_GAS *)&fadt->x_pm_tmr_blk;
	//printf("\nPM_TMR_BLK");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);
	
	gas=(ACPI_GAS *)&fadt->x_gpe0_blk;
	//printf("\nGPE0_BLK");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);
	gas=(ACPI_GAS *)&fadt->x_gpe1_blk;
	//printf("\nGPE1_BLK");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);


	//printf("\nPM1_EVT_LEN=0x%08X", fadt->pm1_evt_len);
	//printf("\nPM1_CNT_LEN=0x%08X", fadt->pm1_cnt_len);
	//printf("\nPM2_CNT_LEN=0x%08X", fadt->pm2_cnt_len);
	//printf("\nPM_TMR_LEN=0x%08X", fadt->pm_tmr_len);
	//printf("\nGPE0_BLK_LEN=0x%08X", fadt->gpe0_blk_len);
	//printf("\nGPE1_BLK_LEN=0x%08X", fadt->gpe1_blk_len);
	
	
	//store register addresses
	gas=(ACPI_GAS *)&fadt->x_pm1a_evt_blk;
	//printf("\nPM1a_EVT_BLK");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);
	__PM1a_STS=gas->address;
	__PM1a_STS_size=(gas->register_bit_width/8)/2;
	__PM1a_EN=gas->address+	((gas->register_bit_width/8)/2);
	__PM1a_EN_size=(gas->register_bit_width/8)/2;

	gas=(ACPI_GAS *)&fadt->x_pm1b_evt_blk;
	//printf("\nPM1b_EVT_BLK");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);
	__PM1b_STS=gas->address;
	__PM1b_STS_size=(gas->register_bit_width/8)/2;
	__PM1b_EN=gas->address+	((gas->register_bit_width/8)/2);
	__PM1b_EN_size=(gas->register_bit_width/8)/2;

	gas=(ACPI_GAS *)&fadt->x_pm1a_cnt_blk;
	//printf("\nPM1a_CNT_BLK");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);
	__PM1_CNTa=gas->address;
	__PM1_CNTa_size=fadt->pm1_cnt_len;

	gas=(ACPI_GAS *)&fadt->x_pm1b_cnt_blk;
	//printf("\nPM1b_CNT_BLK");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);
	__PM1_CNTb=gas->address;
	__PM1_CNTb_size=fadt->pm1_cnt_len;

	printf("\nPM1a_STS=0x%016llx (size=%u bytes)", PM1a_STS, PM1a_STS_SIZE);
	printf("\nPM1a_EN=0x%016llx (size=%u bytes)", PM1a_EN, PM1a_EN_SIZE);
	printf("\nPM1b_STS=0x%016llx (size=%u bytes)", PM1b_STS, PM1b_STS_SIZE);
	printf("\nPM1b_EN=0x%016llx (size=%u bytes)", PM1b_EN, PM1b_EN_SIZE);
	printf("\nPM1_CNTa=0x%016llx (size=%u bytes)", PM1_CNTa, PM1_CNTa_SIZE);
	printf("\nPM1_CNTb=0x%016llx (size=%u bytes)", PM1_CNTb, PM1_CNTb_SIZE);

	//what we need is PM1_CNTa and PM1a_STS register values
	//VTBOX - 804 and 800 respectively (16-bit access)



#if 0	
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
	//printf("\nRESET REG");
	//printf("\nASID=0x%02X, RBW=0x%02X, RBO=0x%02X, AC=0x%02X, Addr=0x%016X", 
	//	gas->address_space_id, gas->register_bit_width, gas->register_bit_offset,
	//			gas->access_size, gas->address);
	//printf("\nRESET VALUE=0x%02x", fadt->reset_value);
	ASSERT(gas->address && gas->address_space_id && (gas->register_bit_width == 8) &&
			(gas->register_bit_offset == 0) );
	__acpi_reset_reg = (u32)gas->address;
	__acpi_reset_reg_val = 	fadt->reset_value;		
#endif			

#endif

	//PM1 status registers (ACPI 4.0a spec, 4.7.3.1.1)
	__PM1a_STS=fadt->pm1a_evt_blk;
	__PM1a_STS_size= (fadt->pm1_evt_len)/2;
	__PM1b_STS=fadt->pm1b_evt_blk;
	__PM1b_STS_size=(fadt->pm1_evt_len)/2;
	
	//PM1 enable registers (ACPI 4.0a spec, 4.7.3.1.2)
	__PM1a_EN=fadt->pm1a_evt_blk + ((fadt->pm1_evt_len)/2);
	__PM1a_EN_size=(fadt->pm1_evt_len)/2;
	__PM1b_EN=fadt->pm1b_evt_blk + ((fadt->pm1_evt_len)/2);
	__PM1b_EN_size=(fadt->pm1_evt_len)/2;

	//PM1 control registers (ACPI 4.0a spec, 4.7.3.2.1)
	__PM1_CNTa=fadt->pm1a_cnt_blk;
	__PM1_CNTa_size=(fadt->pm1_cnt_len)/2;
	__PM1_CNTb=fadt->pm1b_cnt_blk;
	__PM1_CNTb_size=(fadt->pm1_cnt_len)/2;;


	printf("\nPM1a_STS=0x%08x (size=%u bytes)", PM1a_STS, PM1a_STS_SIZE);
	printf("\nPM1a_EN=0x%08x (size=%u bytes)", PM1a_EN, PM1a_EN_SIZE);
	printf("\nPM1b_STS=0x%08x (size=%u bytes)", PM1b_STS, PM1b_STS_SIZE);
	printf("\nPM1b_EN=0x%08x (size=%u bytes)", PM1b_EN, PM1b_EN_SIZE);
	printf("\nPM1_CNTa=0x%08x (size=%u bytes)", PM1_CNTa, PM1_CNTa_SIZE);
	printf("\nPM1_CNTb=0x%08x (size=%u bytes)", PM1_CNTb, PM1_CNTb_SIZE);

	//what we *really* need is PM1_CNTa and PM1a_STS register values


}

