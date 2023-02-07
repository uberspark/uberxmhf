/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
	Pi3 secure boot implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <uart.h>
#include <debug.h>
#include <dmaprot.h>
#include <config.h>

#define SDCMD_WRITE_CMD	0x80
#define SDCMD_READ_CMD	0x40
#define SDCMD_CMD_MASK	0x3f


//activate secure boot protection mechanism
void secboot_activate(void){
	u64 attrs_dev_ro = (LDESC_S2_MC_DEVnGnRE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_READ_ONLY << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_NON_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;


	uapi_s2pgtbl_setprot(BCM2837_EMMC_BASE, attrs_dev_ro);
	sysreg_tlbiallis();

	uapi_s2pgtbl_setprot(BCM2837_SDHOST_BASE, attrs_dev_ro);
	sysreg_tlbiallis();

}



//handle sdio accesses
void secboot_handle_sdio_access(info_intercept_data_abort_t *ida){
	volatile u32 *sdio_reg;

	//we only support 32-bit accesses; bail out if this is not the case
	if(ida->sas != 0x2){
		_XDPRINTFSMP_("%s: invalid sas=%u. Halting!\n", __func__, ida->sas);
		HALT();
	}

	//compute sdio register address
	sdio_reg = (u32 *)ida->pa;

	//act on either writes or reads
	if(ida->wnr){	//intc register write

		//compute value that is going to be written
		u32 guest_value = (u32)guest_regread(ida->r, ida->srt);

		if(sdio_reg == (BCM2837_EMMC_BASE + 0x0c)){
			//_XDPRINTFSMP_("%s: CMD=0x%08x\n", __func__, guest_value);
			u32 cmdop = (guest_value & 0x3F000000UL) >> 24;
			if(cmdop == 24 || cmdop == 25){
				//WRITE block commands
				u32 arg = mmio_read32(BCM2837_EMMC_BASE + 0x08);
				_XDPRINTFSMP_("%s: cmdop=%u(0x%08x), CMD=0x%08x; arg=%u. Halting!\n",
						__func__, cmdop, cmdop, guest_value, arg);
				HALT();
			}

		}

		//just pass-through writes
		mmio_write32(sdio_reg, guest_value);
		//cpu_dsb();
		//cpu_isb();	//synchronize all memory accesses above
		//*sdio_reg = guest_value;

	}else{	//sdio register read
		//we should never get here
		_XDPRINTFSMP_("%s: invalid wnr=%u. Halting!\n", __func__, ida->wnr);
		HALT();
	}

}



//handle sdhost controller accesses
void secboot_handle_sdhost_access(info_intercept_data_abort_t *ida){
	volatile u32 *sdhost_reg;

	//we only support 32-bit accesses; bail out if this is not the case
	if(ida->sas != 0x2){
		_XDPRINTFSMP_("%s: invalid sas=%u. Halting!\n", __func__, ida->sas);
		HALT();
	}

	//compute sdhost register address
	sdhost_reg = (u32 *)ida->pa;

	//act on either writes or reads
	if(ida->wnr){	//intc register write

		//compute value that is going to be written
		u32 guest_value = (u32)guest_regread(ida->r, ida->srt);

		if(sdhost_reg == (BCM2837_SDHOST_BASE + 0x0)){
			//SDCMD register write
			if( guest_value & SDCMD_WRITE_CMD){
				u32 cmdop = guest_value & SDCMD_CMD_MASK;
				if(cmdop == 24 || cmdop == 25){
					//WRITE block commands
					u32 arg = mmio_read32(BCM2837_SDHOST_BASE + 0x04);
					if(arg >= UXMHF_BOOT_PARTITION_START && arg <= UXMHF_BOOT_PARTITION_END){
						_XDPRINTFSMP_("%s: cmdop=%u(0x%08x), SDCMD=0x%08x; arg=%u. Halting!\n",
								__func__, cmdop, cmdop, guest_value, arg);
						HALT();
					}
				}
			}
			//_XDPRINTFSMP_("%s: CMD=0x%08x\n", __func__, guest_value);
		}

		//just pass-through writes
		mmio_write32(sdhost_reg, guest_value);
		//cpu_dsb();
		//cpu_isb();	//synchronize all memory accesses above
		//*sdhost_reg = guest_value;

	}else{	//sdhost register read
		//we should never get here
		_XDPRINTFSMP_("%s: invalid wnr=%u. Halting!\n", __func__, ida->wnr);
		HALT();
	}

}


