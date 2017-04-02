/*
	ARM 8 hypervisor (stage-1) page table translation functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>
#include <guestos.h>

//G4.3
//HYP mode _must_ use long descriptor format

//G4.5.2
//we will use a level-1 pointing to level-2 with 2MB pages
//

//G6.2.69 ARMv8
//HTCR needs to be setup especially T0SZ bit must be 0 to allow full 32-bit addressing

//G6.2.71 ARMv8
//HTTBR is the base address of the page-tables
//base address needs to be 32-byte aligned

//G6.2.66 ARMv8
//HSCTLR has to be set appropriately
//especially the bit 0 M bit enables the MMU
//AFE is 1

//G6.2.100
//MAIR0 and MAIR1 together have 8 memory region attributes
//indexed by attrindx

//G4.5.3
//PXN and nG bits are res0 in HYP mode


void hyppgtbl_initialize(void){
	u32 mair0, mair1;

	mair0 = sysreg_read_mair0();
	mair1 = sysreg_read_mair1();

	_XDPRINTF_("%s: before: mair0=0x%08x, mair1=0x%08x\n", __func__, mair0, mair1);

	mair0 = mair1 = (LDESC_S1_MAIR_HI_OUTER_NON_CACHEABLE | LDESC_S1_MAIR_LO_INNER_NON_CACHEABLE) |
	((LDESC_S1_MAIR_HI_READALLOCATE_WRITEALLOCATE_OUTER_WRITE_BACK_NONTRANSIENT | LDESC_S1_MAIR_LO_READALLOCATE_WRITEALLOCATE_INNER_WRITE_BACK_NONTRANSIENT) << 8) |
	((LDESC_S1_MAIR_HI_OUTER_NON_CACHEABLE | LDESC_S1_MAIR_LO_INNER_NON_CACHEABLE) << 16) |
	((LDESC_S1_MAIR_HI_OUTER_NON_CACHEABLE | LDESC_S1_MAIR_LO_INNER_NON_CACHEABLE) << 24);

	sysreg_write_mair0(mair0);
	sysreg_write_mair1(mair1);

	mair0 = sysreg_read_mair0();
	mair1 = sysreg_read_mair1();

	_XDPRINTF_("%s: after: mair0=0x%08x, mair1=0x%08x\n", __func__, mair0, mair1);

}

__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 hyp_l1_ldesc_table[L1_LDESC_TABLE_MAXENTRIES];
__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 hyp_l2_ldesc_table[L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES];

void hyppgtbl_populate_tables(void){
	u32 i;
	u64 l1_attrs= (LDESC_S1_TABLEATTR_APTABLE_NONE << LDESC_S1_TABLEATTR_APTABLE_SHIFT);
	u64 l2_attrs = (LDESC_S1_AP_READWRITE << LDESC_S1_MEMATTR_AP_SHIFT) |
			(MEM_OUTER_SHAREABLE << LDESC_S1_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK |
			(1 << LDESC_S1_MEMATTR_ATTRINDX_SHIFT);

	//populate l1 ldesc table
	for(i=0; i < L1_LDESC_TABLE_MAXENTRIES; i++){
		if( i < L1_LDESC_TABLE_ENTRIES)
			hyp_l1_ldesc_table[i] = ldesc_make_s1_l1e_table((u32)&hyp_l2_ldesc_table[i * L2_LDESC_TABLE_MAXENTRIES], l1_attrs);
		else
			hyp_l1_ldesc_table[i] = ldesc_make_s1_l1e_invalid();
	}

	//populate l2 ldesc table
	for(i=0; i < (L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES); i++){
		hyp_l2_ldesc_table[i] = ldesc_make_s1_l2e_block( (i * PAGE_SIZE_2M), l2_attrs);
	}


}


void hyppgtbl_loadpgtblbase(void){
	u64 httbr;

	_XDPRINTF_("%s: hyp_l1_desc table at=0x%08x\n", __func__, (u32)&hyp_l1_ldesc_table);

	httbr = sysreg_read_httbr();
	_XDPRINTF_("%s: HTTBR before=0x%016llx\n", __func__, httbr);

	httbr = 0;
	httbr |= ((u64)&hyp_l1_ldesc_table & HTTBR_BADDR_MASK);
	sysreg_write_httbr(httbr);

	httbr = sysreg_read_httbr();
	_XDPRINTF_("%s: HTTBR after=0x%016llx\n", __func__, httbr);
}

