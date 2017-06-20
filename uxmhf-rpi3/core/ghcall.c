/*
 * uxmhf guest hypercall handler hub
 * author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <fdt.h>
#include <debug.h>
#include <dmaprot.h>


//////
// externs
//////
extern bool appnpf_activated;
extern u32 appnpf_page_pa;


void guest_hypercall_handler(arm8_32_regs_t *r, u32 hsr){
	u32 hvc_iss;
	u32 hvc_imm16;

	hvc_iss = ((hsr & HSR_ISS_MASK) >> HSR_ISS_SHIFT);
	hvc_imm16 = hvc_iss & 0x0000FFFFUL;


	if (hvc_imm16 == 1){
		//do nothing; null hypercall

	}else if (hvc_imm16 == 2){
		u64 attrs_noaccess = (LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_BACK_CACHEABLE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_NO_ACCESS << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;

		_XDPRINTFSMP_("%s: setprot_noaccess r0=0x%08x\n", __func__,
				r->r0);

		uapi_s2pgtbl_setprot(r->r0, attrs_noaccess);
		sysreg_tlbiallis();

		appnpf_page_pa = r->r0;
		appnpf_activated=true;

	}else if (hvc_imm16 == 3){
		u64 attrs = (LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_BACK_CACHEABLE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_READ_WRITE << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;

		_XDPRINTFSMP_("%s: setprot_restore-access r0=0x%08x\n", __func__,
				r->r0);

		uapi_s2pgtbl_setprot(r->r0, attrs);
		sysreg_tlbiallis();

		appnpf_page_pa = 0UL;
		appnpf_activated=false;


	}else{
		_XDPRINTFSMP_("%s: unknown HVC instruction imm16=0x%08x. Halting!\n", __func__,
				hvc_imm16);
		HALT();
	}

}
