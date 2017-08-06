/*
	Pi3 root interrupt controller protection implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>
#include <dmaprot.h>

//activate interrupt protection mechanism
void intprot_activate(void){
	u64 attrs_dev_intc = (LDESC_S2_MC_DEVnGnRE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_READ_ONLY << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_NON_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;


	uapi_s2pgtbl_setprot(ARMLOCALREGISTERS_BASE, attrs_dev_intc);
	sysreg_tlbiallis();
}



//handle interrupt controller accesses
void intprot_handle_intcontroller_access(info_intercept_data_abort_t *ida){
	volatile u32 *intc_reg;

	_XDPRINTFSMP_("%s: access at 0x%08x. Halting!\n", __func__, ida->pa);
	HALT();

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

		//just pass-through writes
		//mmio_write32(intc_reg, guest_value);
		cpu_dsb();
		cpu_isb();	//synchronize all memory accesses above
		*intc_reg = guest_value;

	}else{	//intc register read
		//we should never get here
		_XDPRINTFSMP_("%s: invalid wnr=%u. Halting!\n", __func__, ida->wnr);
		HALT();
	}

}

