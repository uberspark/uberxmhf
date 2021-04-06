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
	Pi3 root interrupt controller protection implementation
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/dmaprot.h>
//#include <uberspark/include/uberspark.h>

//activate interrupt protection mechanism
void intprot_activate(void){
	u64 attrs_dev_intc = (LDESC_S2_MC_DEVnGnRE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_READ_ONLY << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_NON_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;


	uapi_s2pgtbl_setprot(ARMLOCALREGISTERS_BASE, attrs_dev_intc);
	CASM_FUNCCALL(sysreg_tlbiallis, CASM_NOPARAM);
}



//handle interrupt controller accesses
void intprot_handle_intcontroller_access(info_intercept_data_abort_t *ida){
	volatile u32 *intc_reg;

	//we only support 32-bit accesses; bail out if this is not the case
	if(ida->sas != 0x2){
		_XDPRINTFSMP_("%s: invalid sas=%u. Halting!\n", __func__, ida->sas);
		HALT();
	}

	//compute interrupt controller register address
	intc_reg = (u32 *)ida->pa;

	//act on either writes or reads
	if(ida->wnr){	//intc register write

		//compute value that is going to be written
		u32 guest_value = (u32)guest_regread(ida->r, ida->srt);

		//ensure HYP timer FIQs are always on
		if(intc_reg == LOCAL_TIMER_INT_CONTROL0){
			if ( !(guest_value & (1UL << 6)) ){
				_XDPRINTFSMP_("%s: FATAL: guest tried to reset HYP timer FIQ. Halting!\n", __func__);
				HALT();
			}
		}

		//just pass-through writes
		//mmio_write32(intc_reg, guest_value);
		CASM_FUNCCALL(cpu_dsb, CASM_NOPARAM);
		CASM_FUNCCALL(cpu_isb, CASM_NOPARAM);	//synchronize all memory accesses above
		*intc_reg = guest_value;

	}else{	//intc register read
		//we should never get here
		_XDPRINTFSMP_("%s: invalid wnr=%u. Halting!\n", __func__, ida->wnr);
		HALT();
	}

}

