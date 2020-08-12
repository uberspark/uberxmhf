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
	ARM 8 hypervisor (stage-1) page table translation functions
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/guestos.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/dmaprot.h>
//#include <uberspark/include/uberspark.h>

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


void hyppgtbl_initialize_memoryattributes(void){
	u32 hmair0, hmair1;

	hmair0 = sysreg_read_hmair0();
	hmair1 = sysreg_read_hmair1();
	_XDPRINTF_("%s: before: hmair0=0x%08x, hmair1=0x%08x\n", __func__, hmair0, hmair1);

	hmair0 = hmair1 = (LDESC_S1_MAIR_HI_DEV | LDESC_S1_MAIR_LO_DEVnGnRnE) |
	((LDESC_S1_MAIR_HI_READALLOCATE_WRITEALLOCATE_OUTER_WRITE_BACK_NONTRANSIENT | LDESC_S1_MAIR_LO_READALLOCATE_WRITEALLOCATE_INNER_WRITE_BACK_NONTRANSIENT) << 8) |
	((LDESC_S1_MAIR_HI_OUTER_NON_CACHEABLE | LDESC_S1_MAIR_LO_INNER_NON_CACHEABLE) << 16) |
	((LDESC_S1_MAIR_HI_DEV | LDESC_S1_MAIR_LO_DEVnGnRE) << 24);

	sysreg_write_hmair0(hmair0);
	sysreg_write_hmair1(hmair1);

	hmair0 = sysreg_read_hmair0();
	hmair1 = sysreg_read_hmair1();
	_XDPRINTF_("%s: after: hmair0=0x%08x, hmair1=0x%08x\n", __func__, hmair0, hmair1);
}




void hyppgtbl_initialize_translationcontrol(void){
	u32 htcr;

	htcr = sysreg_read_htcr();
	_XDPRINTF_("%s: HTCR before=0x%08x\n", __func__, htcr);

	htcr &= HTCR_IMPDEF_MASK;	//clear out everything except implementation defined bits
	htcr |= HTCR_RES1_MASK;	//reserved 1 bits
	htcr |= ((0x0 << HTCR_T0SZ_SHIFT) & HTCR_T0SZ_MASK);	//T0SZ=0; 32 bits physical address
	htcr |= ((MEM_WRITEBACK_READALLOCATE_WRITEALLOCATE << HTCR_IRGN0_SHIFT) & HTCR_IRGN0_MASK);	//L1 cache attribute
	htcr |= ((MEM_WRITEBACK_READALLOCATE_WRITEALLOCATE << HTCR_ORGN0_SHIFT) & HTCR_ORGN0_MASK);	//L2 cache attribute
	//htcr |= ((MEM_NON_CACHEABLE << HTCR_IRGN0_SHIFT) & HTCR_IRGN0_MASK);	//L1 cache attribute
	//htcr |= ((MEM_NON_CACHEABLE << HTCR_ORGN0_SHIFT) & HTCR_ORGN0_MASK);	//L2 cache attribute
	htcr |= ((MEM_INNER_SHAREABLE << HTCR_SH0_SHIFT) & HTCR_SH0_MASK);	//shareability attribute

	sysreg_write_htcr(htcr);

	htcr = sysreg_read_htcr();
	_XDPRINTF_("%s: HTCR after=0x%08x\n", __func__, htcr);
}

__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 hyp_l1_ldesc_table[L1_LDESC_TABLE_MAXENTRIES];
__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 hyp_l2_ldesc_table[L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES];

extern dmac_cb_t dmac_cblist[BCM2837_DMA_NUMCHANNELS][BCM2837_DMA_MAXCBRECORDS];


void hyppgtbl_populate_tables(void){
	u32 i;
	u64 l1_attrs= (LDESC_S1_TABLEATTR_APTABLE_NONE << LDESC_S1_TABLEATTR_APTABLE_SHIFT);
	//u64 l2_attrs = (LDESC_S1_AP_READWRITE << LDESC_S1_MEMATTR_AP_SHIFT) |
	//		(MEM_INNER_SHAREABLE << LDESC_S1_MEMATTR_SH_SHIFT) |
	//		LDESC_S1_MEMATTR_AF_MASK |
	//		(1 << LDESC_S1_MEMATTR_ATTRINDX_SHIFT);

	u64 l2_attrs = (LDESC_S1_AP_READWRITE << LDESC_S1_MEMATTR_AP_SHIFT) |
			(MEM_INNER_SHAREABLE << LDESC_S1_MEMATTR_SH_SHIFT) |
			LDESC_S1_MEMATTR_AF_MASK |
			(1 << LDESC_S1_MEMATTR_ATTRINDX_SHIFT);

	u64 l2_attrs_nc = (LDESC_S1_AP_READWRITE << LDESC_S1_MEMATTR_AP_SHIFT) |
			(MEM_INNER_SHAREABLE << LDESC_S1_MEMATTR_SH_SHIFT) |
			LDESC_S1_MEMATTR_AF_MASK |
			(2 << LDESC_S1_MEMATTR_ATTRINDX_SHIFT);


	u64 l2_attrs_dev = (LDESC_S1_AP_READWRITE << LDESC_S1_MEMATTR_AP_SHIFT) |
			(MEM_NON_SHAREABLE << LDESC_S1_MEMATTR_SH_SHIFT) |
			LDESC_S1_MEMATTR_AF_MASK |
			(3 << LDESC_S1_MEMATTR_ATTRINDX_SHIFT);


	//populate l1 ldesc table
	for(i=0; i < L1_LDESC_TABLE_MAXENTRIES; i++){
		if( i < L1_LDESC_TABLE_ENTRIES)
			hyp_l1_ldesc_table[i] = ldesc_make_s1_l1e_table((u32)&hyp_l2_ldesc_table[i * L2_LDESC_TABLE_MAXENTRIES], l1_attrs);
			//hyp_l1_ldesc_table[i] = ldesc_make_s1_l1e_block((i * PAGE_SIZE_1G), l2_attrs);
		else
			hyp_l1_ldesc_table[i] = ldesc_make_s1_l1e_invalid();
	}


	//debug
	_XDPRINTF_("%s: dumping l1 ldesc table...\n", __func__);
	for(i=0; i < L1_LDESC_TABLE_ENTRIES; i++){
		_XDPRINTF_(" %u-> %016llx\n", i, hyp_l1_ldesc_table[i]);
	}
	_XDPRINTF_("%s: l1 ldesc table dump finished\n", __func__);
	_XDPRINTF_("%s: dmac_cblist at 0x%08x\n", __func__, (u32)&dmac_cblist);

	//populate l2 ldesc table
	for(i=0; i < (L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES); i++){
		if ( ((i * PAGE_SIZE_2M) >= UXMHF_CORE_START_ADDR) &&
				((i * PAGE_SIZE_2M) < UXMHF_CORE_END_ADDR)	){
			//hypervisor memory region mapping
			if ( (i * PAGE_SIZE_2M) == (u32)&dmac_cblist ){
				hyp_l2_ldesc_table[i] = ldesc_make_s1_l2e_block( (i * PAGE_SIZE_2M), l2_attrs_nc);
				_XDPRINTF_("%s: mapped dmac_cblist at 0x%08x\n", __func__, (u32)&dmac_cblist);
			}else{
				hyp_l2_ldesc_table[i] = ldesc_make_s1_l2e_block( (i * PAGE_SIZE_2M), l2_attrs);
			}

		}else if ( (i * PAGE_SIZE_2M) >= BCM2837_PERIPHERALS_BASE ){
			hyp_l2_ldesc_table[i] = ldesc_make_s1_l2e_block( (i * PAGE_SIZE_2M), l2_attrs_dev);

		}else if ( ((i * PAGE_SIZE_2M) >= 0x3AC00000) && ((i * PAGE_SIZE_2M) < BCM2837_PERIPHERALS_BASE) ){
			//TBD: track guest MAIR
			hyp_l2_ldesc_table[i] = ldesc_make_s1_l2e_block( (i * PAGE_SIZE_2M), l2_attrs_nc);

		}else{
			hyp_l2_ldesc_table[i] = ldesc_make_s1_l2e_block( (i * PAGE_SIZE_2M), l2_attrs);
		}
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


void hyppgtbl_activate(void){
	u32 hsctlr;
	_XDPRINTF_("%s: [ENTER]\n", __func__);

	hyppgtbl_initialize_memoryattributes();
	_XDPRINTF_("%s: initialized memory attributes\n", __func__);

	hyppgtbl_initialize_translationcontrol();
	_XDPRINTF_("%s: initialized translation control\n", __func__);

	hyppgtbl_loadpgtblbase();
	_XDPRINTF_("%s: loaded page-table base register\n", __func__);

	mmu_disableicache();
	_XDPRINTF_("%s: disabled icache\n", __func__);

	mmu_disabledcache();
	_XDPRINTF_("%s: disabled dcache\n", __func__);

	mmu_invalidatetlbs();
	_XDPRINTF_("%s: invalidated TLBs\n", __func__);

	mmu_invalidateicache();
	_XDPRINTF_("%s: invalidated icache\n", __func__);

	mmu_activatetranslation();
	_XDPRINTF_("%s: MMU translation activated\n", __func__);

	//mmu_enableicache();
	//_XDPRINTF_("%s: enabled icache\n", __func__);

	//mmu_enabledcache();
	//_XDPRINTF_("%s: enabled dcache\n", __func__);

	hsctlr = sysreg_read_hsctlr();
	_XDPRINTF_("%s: [EXIT] HSCTLR=0x%08x\n", __func__, hsctlr);
}
