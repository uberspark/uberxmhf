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

// EMHF memory protection component
// intel VMX arch. backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>

//----------------------------------------------------------------------
// Structure that captures fixed MTRR properties
struct _fixed_mtrr_prop_t {
	u32 msr;	/* MSR register address (ECX in RDMSR / WRMSR) */
	u32 start;	/* Start address */
	u32 step;	/* Size of each range */
	u32 end;	/* End address (start + 8 * step == end) */
} fixed_mtrr_prop[NUM_FIXED_MTRRS] = {
	{IA32_MTRR_FIX64K_00000, 0x00000000, 0x00010000, 0x00080000},
	{IA32_MTRR_FIX16K_80000, 0x00080000, 0x00004000, 0x000A0000},
	{IA32_MTRR_FIX16K_A0000, 0x000A0000, 0x00004000, 0x000C0000},
	{IA32_MTRR_FIX4K_C0000, 0x000C0000, 0x00001000, 0x000C8000},
	{IA32_MTRR_FIX4K_C8000, 0x000C8000, 0x00001000, 0x000D0000},
	{IA32_MTRR_FIX4K_D0000, 0x000D0000, 0x00001000, 0x000D8000},
	{IA32_MTRR_FIX4K_D8000, 0x000D8000, 0x00001000, 0x000E0000},
	{IA32_MTRR_FIX4K_E0000, 0x000E0000, 0x00001000, 0x000E8000},
	{IA32_MTRR_FIX4K_E8000, 0x000E8000, 0x00001000, 0x000F0000},
	{IA32_MTRR_FIX4K_F0000, 0x000F0000, 0x00001000, 0x000F8000},
	{IA32_MTRR_FIX4K_F8000, 0x000F8000, 0x00001000, 0x00100000},
};

//----------------------------------------------------------------------
// local (static) support function forward declarations
static void _vmx_gathermemorytypes(VCPU *vcpu);
static u32 _vmx_getmemorytypeforphysicalpage(VCPU *vcpu, u64 pagebaseaddr);
static void _vmx_setupEPT(VCPU *vcpu);

//======================================================================
// global interfaces (functions) exported by this component

// initialize memory protection structures for a given core (vcpu)
void xmhf_memprot_arch_x86vmx_initialize(VCPU *vcpu){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);

	_vmx_gathermemorytypes(vcpu);
#ifndef __XMHF_VERIFICATION__
	_vmx_setupEPT(vcpu);
#endif

	//enable EPT
	vcpu->vmcs.control_VMX_seccpu_based |= (1U << VMX_SECPROCBASED_ENABLE_EPT);
	//enable VPID
	vcpu->vmcs.control_VMX_seccpu_based |= (1U << VMX_SECPROCBASED_ENABLE_VPID);
	//VPID=0 is reserved for hypervisor
	vcpu->vmcs.control_vpid = 1;
	//page walk of 4 and WB memory
	vcpu->vmcs.control_EPT_pointer = hva2spa((void*)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E;
	//disable CR3 load exiting
	vcpu->vmcs.control_VMX_cpu_based &= ~(1U << VMX_PROCBASED_CR3_LOAD_EXITING);
	//disable CR3 store exiting
	vcpu->vmcs.control_VMX_cpu_based &= ~(1U << VMX_PROCBASED_CR3_STORE_EXITING);
}


//----------------------------------------------------------------------
// local (static) support functions follow

/* Check whether an MTRR type is valid, return 1 on valid, or 0 on invalid */
static u32 _vmx_mtrr_checktype(u32 type) {
	return (type == 0 || type == 1 || type == 4 || type == 5 || type == 6);
}

/*
 * Check whether IA32_MTRR_DEF_TYPE value is valid
 * When valid, the following pointers are filled; when invalid, pointers not
 * modified.
 * pe: whether MTRRs are enabled
 * pfe: whether fixed MTRRs are enabled
 * ptype: default mtrr type
 */
static u32 _vmx_mtrr_checkdeftype(u64 msrval, u32 *pe, u32 *pfe, u32 *ptype) {
	u32 e, fe, type;
	/* Check reserved bits */
	if (msrval & ~0xCFFULL) {
		return 0;
	}
	e = (msrval & 0x800U) ? 1 : 0;
	fe = (msrval & 0x400U) ? 1 : 0;
	type = msrval & 0xFFU;
	/* If MTRRs are enabled, make sure type is valid */
	if (e && _vmx_mtrr_checktype(type) == 0) {
		return 0;
	}
	*pe = e;
	*pfe = fe;
	*ptype = type;
	return 1;
}

/* Check whether a fixed MTRR is valid (e.g. IA32_MTRR_FIX64K_00000) */
static u32 _vmx_mtrr_checkfixed(u64 msrval) {
	u32 i = 0;
    for (i = 0; i < 8; i++) {
		if (!_vmx_mtrr_checktype((u8) (msrval >> (i * 8)))) {
			return 0;
		}
	}
	return 1;
}

/* Check whether a variable MTRR is valid (e.g. IA32_MTRR_PHYSBASE0) */
static u32 _vmx_mtrr_checkvariable(VCPU *vcpu, u64 baseval, u64 maskval) {
	u32 v, type;
	/* Check reserved bits */
	if (baseval & ~(vcpu->vmx_ept_paddrmask | 0xFFULL)) {
		return 0;
	}
	if (maskval & ~(vcpu->vmx_ept_paddrmask | 0x800ULL)) {
		return 0;
	}
	v = maskval & 0x800U;
	type = baseval & 0xFFU;
	if (v && _vmx_mtrr_checktype(type) == 0) {
		return 0;
	}
	return 1;
}

//---gather memory types for system physical memory------------------------------
static void _vmx_gathermemorytypes(VCPU *vcpu){
 	u32 eax, ebx, ecx, edx;
	u32 num_vmtrrs=0;	//number of variable length MTRRs supported by the CPU
    u32 i = 0;

	//0. sanity check
  	//check MTRR support
  	eax=0x00000001;
  	ecx=0x00000000;
	#ifndef __XMHF_VERIFICATION__
  	asm volatile ("cpuid\r\n"
            :"=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
            :"a"(eax), "c" (ecx));
  	#endif

  	if( !(edx & (u32)(1 << 12)) ){
  		printf("CPU(0x%02x): CPU does not support MTRRs!\n", vcpu->id);
  		HALT();
  	}

  	//check MTRR caps
  	rdmsr(IA32_MTRRCAP, &eax, &edx);
	num_vmtrrs = (u8)eax;
	vcpu->vmx_guestmtrrmsrs.var_count = num_vmtrrs;
	printf("IA32_MTRRCAP: VCNT=%u, FIX=%u, WC=%u, SMRR=%u\n",
			num_vmtrrs, ((eax & (1 << 8)) >> 8),  ((eax & (1 << 10)) >> 10),
			((eax & (1 << 11)) >> 11));
	//sanity check that fixed MTRRs are supported
	HALT_ON_ERRORCOND( ((eax & (1 << 8)) >> 8) );
	//ensure number of variable MTRRs are within the maximum supported
	HALT_ON_ERRORCOND( (num_vmtrrs <= MAX_VARIABLE_MTRR_PAIRS) );

	// Obtain MAXPHYADDR and compute paddrmask
	{
		u32 eax, ebx, ecx, edx;
		/* Check whether CPUID 0x80000008 is supported */
		cpuid(0x80000000U, &eax, &ebx, &ecx, &edx);
		HALT_ON_ERRORCOND(eax >= 0x80000008U);
		/* Compute paddrmask from CPUID.80000008H:EAX[7:0] (max phy addr) */
		cpuid(0x80000008U, &eax, &ebx, &ecx, &edx);
		eax &= 0xFFU;
		HALT_ON_ERRORCOND(eax >= 32 && eax < 64);
		vcpu->vmx_ept_paddrmask = (1ULL << eax) - 0x1000ULL;
	}

	// Read MTRR default type register
	{
		u32 valid;
		u64 msrval = rdmsr64(IA32_MTRR_DEF_TYPE);
		vcpu->vmx_guestmtrrmsrs.def_type = msrval;
		valid = _vmx_mtrr_checkdeftype(msrval, &vcpu->vmx_ept_mtrr_enable,
										&vcpu->vmx_ept_fixmtrr_enable,
										&vcpu->vmx_ept_defaulttype);
		HALT_ON_ERRORCOND(valid);
	}

	// Fill guest MTRR shadow MSRs
	for (i = 0; i < NUM_FIXED_MTRRS; i++) {
		u64 val = rdmsr64(fixed_mtrr_prop[i].msr);
		HALT_ON_ERRORCOND(_vmx_mtrr_checkfixed(val));
		vcpu->vmx_guestmtrrmsrs.fix_mtrrs[i] = val;
	}
	for (i = 0; i < num_vmtrrs; i++) {
		u64 baseval = rdmsr64(IA32_MTRR_PHYSBASE0 + 2 * i);
		u64 maskval = rdmsr64(IA32_MTRR_PHYSMASK0 + 2 * i);
		HALT_ON_ERRORCOND(_vmx_mtrr_checkvariable(vcpu, baseval, maskval));
		vcpu->vmx_guestmtrrmsrs.var_mtrrs[i].base = baseval;
		vcpu->vmx_guestmtrrmsrs.var_mtrrs[i].mask = maskval;
	}
}

//---get memory type for a given physical page address--------------------------
//
//11.11.4.1 MTRR Precedences
//  0. if MTRRs are not enabled --> MTRR_TYPE_UC
//  if enabled then
     //if physaddr < 1MB use fixed MTRR ranges return type
     //else if within a valid variable range MTRR then
        //if a single match, return type
        //if two or more and one is UC, return UC
        //if two or more and WB and WT, return WT
        //else invalid combination
     //else
       // return default memory type
//
static u32 _vmx_getmemorytypeforphysicalpage(VCPU *vcpu, u64 pagebaseaddr){
	u32 prev_type = MTRR_TYPE_RESV;
    u32 i = 0;

	/* If MTRRs not enabled, return UC */
	if (!vcpu->vmx_ept_mtrr_enable) {
		return MTRR_TYPE_UC;
	}
	/* If fixed MTRRs are enabled, and addr < 1M, use them */
	if (pagebaseaddr < 0x100000ULL && vcpu->vmx_ept_fixmtrr_enable) {
		for (i = 0; i < NUM_FIXED_MTRRS; i++) {
			struct _fixed_mtrr_prop_t *prop = &fixed_mtrr_prop[i];
			if (pagebaseaddr < prop->end) {
				u32 index = (prop->start - pagebaseaddr) / prop->step;
				u64 msrval = vcpu->vmx_guestmtrrmsrs.fix_mtrrs[i];
				return (u8) (msrval >> (index * 8));
			}
		}
		/*
		 * Should be impossible because the last entry in fixed_mtrr_prop is 1M.
		 */
		HALT_ON_ERRORCOND(0 && "Unknown fixed MTRR");
	}
	/* Compute variable MTRRs */
	for (i = 0; i < vcpu->vmx_guestmtrrmsrs.var_count; i++) {
		u64 base = vcpu->vmx_guestmtrrmsrs.var_mtrrs[i].base;
		u64 mask = vcpu->vmx_guestmtrrmsrs.var_mtrrs[i].mask;
		u32 cur_type = base & 0xFFU;
		/* Check valid bit */
		if (!(mask & (1ULL << 11))) {
			continue;
		}
		/* Clear lower bits, test whether address in range */
		base &= ~0xFFFULL;
		mask &= ~0xFFFULL;
		if ((pagebaseaddr & mask) != (base & mask)) {
			continue;
		}
		/* Check for conflict resolutions: UC + * = UC; WB + WT = WT */
		if (prev_type == MTRR_TYPE_RESV || prev_type == cur_type) {
			prev_type = cur_type;
		} else if (prev_type == MTRR_TYPE_UC || cur_type == MTRR_TYPE_UC) {
			prev_type = MTRR_TYPE_UC;
		} else if (prev_type == MTRR_TYPE_WB && cur_type == MTRR_TYPE_WT) {
			prev_type = MTRR_TYPE_WT;
		} else if (prev_type == MTRR_TYPE_WT && cur_type == MTRR_TYPE_WB) {
			prev_type = MTRR_TYPE_WT;
		} else {
			printf("Conflicting MTRR types (%u, %u), HALT!\n", prev_type, cur_type);
			HALT();
		}
	}
	/* If not covered by any MTRR, use default type */
	if (prev_type == MTRR_TYPE_RESV) {
		prev_type = vcpu->vmx_ept_defaulttype;
	}
	return prev_type;
}


//---setup EPT for VMX----------------------------------------------------------
static void _vmx_setupEPT(VCPU *vcpu){
	//step-1: tie in EPT PML4 structures
	u64 *pml4_entry = (u64 *)vcpu->vmx_vaddr_ept_pml4_table;
	u64 *pdp_entry = (u64 *)vcpu->vmx_vaddr_ept_pdp_table;
	u64 *pd_entry = (u64 *)vcpu->vmx_vaddr_ept_pd_tables;
	u64 *p_entry = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
	u64 pdp_table = hva2spa((void*)vcpu->vmx_vaddr_ept_pdp_table);
	u64 pd_table = hva2spa((void*)vcpu->vmx_vaddr_ept_pd_tables);
	u64 p_table = hva2spa((void*)vcpu->vmx_vaddr_ept_p_tables);
	// TODO: for amd64, likely can use 1G / 2M pages.
	// If so, also need to change _vmx_getmemorytypeforphysicalpage()
    gpa_t paddr = 0;

	for (paddr = 0; paddr < MAX_PHYS_ADDR; paddr += PA_PAGE_SIZE_4K) {
		if (PA_PAGE_ALIGNED_512G(paddr)) {
			/* Create PML4E */
			gpa_t i = paddr >> PAGE_SHIFT_512G;
			pml4_entry[i] = (pdp_table + (i << PAGE_SHIFT_4K)) | 0x7;
		}
		if (PA_PAGE_ALIGNED_1G(paddr)) {
			/* Create PDPE */
			gpa_t i = paddr >> PAGE_SHIFT_1G;
			pdp_entry[i] = (pd_table + (i << PAGE_SHIFT_4K)) | 0x7;
		}
		if (PA_PAGE_ALIGNED_2M(paddr)) {
			/* Create PDE */
			gpa_t i = paddr >> PAGE_SHIFT_2M;
			pd_entry[i] = (p_table + (i << PAGE_SHIFT_4K)) | 0x7;
		}
		/* PA_PAGE_ALIGNED_4K */
		{
			/* Create PE */
			gpa_t i = paddr >> PAGE_SHIFT_4K;
			u64 memorytype = _vmx_getmemorytypeforphysicalpage(vcpu, paddr);
			u64 lower;
			/*
			 * For memorytype equal to 0 (UC), 1 (WC), 4 (WT), 5 (WP), 6 (WB),
			 * MTRR memory type and EPT memory type are the same encoding.
			 * Currently other encodings are reserved.
			 */
			HALT_ON_ERRORCOND(memorytype == 0 || memorytype == 1 ||
								memorytype == 4 || memorytype == 5 ||
								memorytype == 6);
			if ((paddr >= (rpb->XtVmmRuntimePhysBase - PA_PAGE_SIZE_2M)) &&
				(paddr < (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize))) {
				lower = 0x0;	/* not present */
			} else {
				lower = 0x7;	/* present */
			}
			p_entry[i] = paddr | (memorytype << 3) | lower;
		}
	}
}

/*
 * Update EPT in respond to change in memory type (usually MTRRs)
 * start: start of address range to be updated
 * end: end of address range to be updated
 */
static void _vmx_updateEPT_memtype(VCPU *vcpu, u64 start, u64 end){
	u64 *p_entry = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
    u64 paddr = 0;

	HALT_ON_ERRORCOND(PA_PAGE_ALIGNED_4K(start));
	HALT_ON_ERRORCOND(PA_PAGE_ALIGNED_4K(end));
	for (paddr = start; paddr < end; paddr += PA_PAGE_SIZE_4K) {
		u64 i = paddr / PA_PAGE_SIZE_4K;
		u64 memorytype = _vmx_getmemorytypeforphysicalpage(vcpu, paddr);
		HALT_ON_ERRORCOND(memorytype == 0 || memorytype == 1 ||
							memorytype == 4 || memorytype == 5 ||
							memorytype == 6);
		p_entry[i] = (p_entry[i] & ~0x38ULL) | (memorytype << 3);
	}
}

/*
 * Read a guest MTRR value from shadow, return 0 if successful read,
 * return non-zero if unsuccessful read (should report error to guest OS)
 */
u32 xmhf_memprot_arch_x86vmx_mtrr_read(VCPU *vcpu, u32 msr, u64 *val) {
    u32 i = 0;

	if (msr == IA32_MTRR_DEF_TYPE) {
		/* Default type register */
		*val = vcpu->vmx_guestmtrrmsrs.def_type;
		return 0;
	} else if (IA32_MTRR_PHYSBASE0 <= msr &&
		msr <= IA32_MTRR_PHYSMASK0 + 2 * vcpu->vmx_guestmtrrmsrs.var_count) {
		/* Variable MTRR */
		if ((msr - IA32_MTRR_PHYSBASE0) % 2 == 0) {
			u32 index = (msr - IA32_MTRR_PHYSBASE0) / 2;
			*val = vcpu->vmx_guestmtrrmsrs.var_mtrrs[index].base;
		} else {
			u32 index = (msr - IA32_MTRR_PHYSMASK0) / 2;
			*val = vcpu->vmx_guestmtrrmsrs.var_mtrrs[index].mask;
		}
		return 0;
	} else {
		/* Fixed MTRR */
		for (i = 0; i < NUM_FIXED_MTRRS; i++) {
			if (fixed_mtrr_prop[i].msr == msr) {
				*val = vcpu->vmx_guestmtrrmsrs.fix_mtrrs[i];
				return 0;
			}
		}
		printf("Cannot find MTRR, the caller (XMHF code) is wrong.\n");
		HALT();
		/* Placate compiler */
		return 1;
	}
}

/*
 * Write a guest MTRR value to shadow and update EPT, return 0 if successful,
 * return non-zero if unsuccessful write (should report error to guest OS)
 */
u32 xmhf_memprot_arch_x86vmx_mtrr_write(VCPU *vcpu, u32 msr, u64 val) {
	u32 hypapp_status;
	u64 skip_ept_update = 0;
	/* Logging */
	{
		u64 oldval;
		HALT_ON_ERRORCOND(xmhf_memprot_arch_x86vmx_mtrr_read(vcpu, msr, &oldval) == 0);
		printf("CPU(0x%02x): WRMSR (MTRR) 0x%08x 0x%016llx (old = 0x%016llx)\n",
				vcpu->id, msr, val, oldval);
	}
	/*
	 * Check whether hypapp allows modifying MTRR
	 *
	 * TODO: For TrustVisor, there is a corner case race condition:
	 * 1. CPU X calls xmhf_app_handlemtrr() and returns
	 * 2. CPU Y starts TrustVisor business, which modifies EPT01
	 * 3. CPU X calls _vmx_updateEPT_memtype(), which modifies EPT01
	 *
	 * A possible workaround is to call xmhf_app_handlemtrr() after
	 * _vmx_updateEPT_memtype(). However this does not work if the hypapp has
	 * special MTRR handling code.
	 */
	hypapp_status = xmhf_app_handlemtrr(vcpu, msr, val);
	if (hypapp_status != APP_SUCCESS) {
		printf("CPU(0x%02x): Hypapp does not allow changing MTRRs. Halt!\n",
				vcpu->id);
		HALT();
	}
	if (msr == IA32_MTRR_DEF_TYPE) {
		/* Default type register */
		if (val == vcpu->vmx_guestmtrrmsrs.def_type) {
			/* No change to MSR value */
			return 0;
		}
		if (!_vmx_mtrr_checkdeftype(val, &vcpu->vmx_ept_mtrr_enable,
									&vcpu->vmx_ept_fixmtrr_enable,
									&vcpu->vmx_ept_defaulttype)) {
			return 1;
		}
		vcpu->vmx_guestmtrrmsrs.def_type = val;
	} else if (IA32_MTRR_PHYSBASE0 <= msr &&
		msr <= IA32_MTRR_PHYSMASK0 + 2 * vcpu->vmx_guestmtrrmsrs.var_count) {
		/* Variable MTRR */
		u32 index;
		u64 baseval = val, maskval = val;
		if ((msr - IA32_MTRR_PHYSBASE0) % 2 == 0) {
			/* Want to set baseval, retrieve maskval from shadow */
			index = (msr - IA32_MTRR_PHYSBASE0) / 2;
			maskval = vcpu->vmx_guestmtrrmsrs.var_mtrrs[index].mask;
			if (baseval == vcpu->vmx_guestmtrrmsrs.var_mtrrs[index].base) {
				/* No change to MSR value */
				return 0;
			}
		} else {
			/* Want to set maskval, retrieve baseval from shadow */
			index = (msr - IA32_MTRR_PHYSMASK0) / 2;
			baseval = vcpu->vmx_guestmtrrmsrs.var_mtrrs[index].base;
			if (maskval == vcpu->vmx_guestmtrrmsrs.var_mtrrs[index].mask) {
				/* No change to MSR value */
				return 0;
			}
		}
		/* Sanity check */
		if (!_vmx_mtrr_checkvariable(vcpu, baseval, maskval)) {
			return 1;
		}
		/* Only one write will be effective, but this saves if-else blocks */
		vcpu->vmx_guestmtrrmsrs.var_mtrrs[index].base = baseval;
		vcpu->vmx_guestmtrrmsrs.var_mtrrs[index].mask = maskval;
		/* If MTRRs are not enabled, no need to update EPT */
		if (!vcpu->vmx_ept_mtrr_enable) {
			skip_ept_update = 1;
		}
	} else {
		/* Fixed MTRR */
		u32 found = 0;
        u32 i = 0;

		if (!_vmx_mtrr_checkfixed(val)) {
			return 1;
		}
		for (i = 0; i < NUM_FIXED_MTRRS; i++) {
			if (fixed_mtrr_prop[i].msr == msr) {
				if (val == vcpu->vmx_guestmtrrmsrs.fix_mtrrs[i]) {
					/* No change to MSR value */
					return 0;
				}
				vcpu->vmx_guestmtrrmsrs.fix_mtrrs[i] = val;
				found = 1;
				break;
			}
		}
		if (!found) {
			printf("Cannot find MTRR, the caller (XMHF code) is wrong.\n");
			HALT();
		}
		/* If MTRRs / fixed MTRRs are not enabled, no need to update EPT */
		if (!vcpu->vmx_ept_mtrr_enable || !vcpu->vmx_ept_fixmtrr_enable) {
			skip_ept_update = 1;
		}
	}

	/* Update EPT and flush EPT's TLB */
	if (!skip_ept_update) {
		/*
		 * Currently updating all of EPT (from 0 to MAX_PHYS_ADDR). It is
		 * possible to only update a part of EPT, depending on what MTRR is
		 * changed and the value before and after change. However, this needs a
		 * complicated logic.
		 */
		printf("CPU(0x%02x): Update EPT memory types due to MTRR\n", vcpu->id);
		_vmx_updateEPT_memtype(vcpu, 0, MAX_PHYS_ADDR);
		xmhf_memprot_arch_x86vmx_flushmappings_localtlb(vcpu);
	}
	return 0;
}

//flush hardware page table mappings (TLB)
void xmhf_memprot_arch_x86vmx_flushmappings(VCPU *vcpu){
  HALT_ON_ERRORCOND(__vmx_invept(VMX_INVEPT_SINGLECONTEXT,
                                 (u64)vcpu->vmcs.control_EPT_pointer));
}

//flush hardware page table mappings (TLB)
void xmhf_memprot_arch_x86vmx_flushmappings_localtlb(VCPU *vcpu){
  (void)vcpu;
  HALT_ON_ERRORCOND(__vmx_invept(VMX_INVEPT_GLOBAL,
                                 (u64)0));
}

//set protection for a given physical memory address
void xmhf_memprot_arch_x86vmx_setprot(VCPU *vcpu, u64 gpa, u32 prottype){
  u32 pfn;
  u64 *pt;
  u32 flags =0;

#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
   	assert ( (vcpu != NULL) );
	assert ( ( (gpa < rpb->XtVmmRuntimePhysBase) ||
							 (gpa >= (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize))
						   ) );
	assert ( ( (prottype > 0)	&&
	                         (prottype <= MEMP_PROT_MAXVALUE)
	                       ) );
	assert (
	 (prottype == MEMP_PROT_NOTPRESENT) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READONLY) && (prottype & MEMP_PROT_EXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READWRITE) && (prottype & MEMP_PROT_EXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READONLY) && (prottype & MEMP_PROT_NOEXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READWRITE) && (prottype & MEMP_PROT_NOEXECUTE))
	);
#endif

  pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;

  //default is not-present, read-only, no-execute
  pt[pfn] &= ~(u64)7; //clear all previous flags

  //map high level protection type to EPT protection bits
  if(prottype & MEMP_PROT_PRESENT){
	flags=1;	//present is defined by the read bit in EPT

	if(prottype & MEMP_PROT_READWRITE)
		flags |= 0x2;

	if(prottype & MEMP_PROT_EXECUTE)
		flags |= 0x4;
  }

  //set new flags
  pt[pfn] |= flags;
}


//get protection for a given physical memory address
u32 xmhf_memprot_arch_x86vmx_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  u64 entry = pt[pfn];
  u32 prottype;

  if(! (entry & 0x1) ){
	prottype = MEMP_PROT_NOTPRESENT;
	return prottype;
  }

  prottype = MEMP_PROT_PRESENT;

  if( entry & 0x2 )
	prottype |= MEMP_PROT_READWRITE;
  else
	prottype |= MEMP_PROT_READONLY;

  if( entry & 0x4 )
	prottype |= MEMP_PROT_EXECUTE;
  else
	prottype |= MEMP_PROT_NOEXECUTE;

  return prottype;
}

u64 xmhf_memprot_arch_x86vmx_get_EPTP(VCPU *vcpu)
{
  HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
  return vcpu->vmcs.control_EPT_pointer;
}
void xmhf_memprot_arch_x86vmx_set_EPTP(VCPU *vcpu, u64 eptp)
{
  HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
  vcpu->vmcs.control_EPT_pointer = eptp;
}
