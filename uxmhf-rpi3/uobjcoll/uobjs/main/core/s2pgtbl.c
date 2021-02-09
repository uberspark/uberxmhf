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
	ARM 8 stage-2 page table translation functions
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/guestos.h>
//#include <uberspark/include/uberspark.h>

/* setup CPU to support stage-2 table translation */
void s2pgtbl_initialize(void){
	u32 vtcr, hdcr, hcptr, hstr;

	vtcr = sysreg_read_vtcr();
	uart_puts("VTCR before= ");
	//debug_hexdumpu32(vtcr);

	vtcr = 0;
	vtcr |= VTCR_RES1_MASK;	//reserved 1 bits
	//vtcr |= ((0x8 << VTCR_T0SZ_SHIFT) & VTCR_T0SZ_MASK);	//T0SZ=-8; 40 bits physical address
	//vtcr |= ((1 << VTCR_S_SHIFT) & VTCR_S_MASK);		//S=1
	vtcr |= ((0x0 << VTCR_T0SZ_SHIFT) & VTCR_T0SZ_MASK);	//T0SZ=0; 32 bits physical address
	vtcr |= ((0 << VTCR_S_SHIFT) & VTCR_S_MASK);		//S=0
	vtcr |= ((1 << VTCR_SL0_SHIFT) & VTCR_SL0_MASK);	//SL0=1; 3-level page table
	vtcr |= ((MEM_WRITEBACK_READALLOCATE_WRITEALLOCATE << VTCR_IRGN0_SHIFT) & VTCR_IRGN0_MASK);	//L1 cache attribute
	vtcr |= ((MEM_WRITEBACK_READALLOCATE_WRITEALLOCATE << VTCR_ORGN0_SHIFT) & VTCR_ORGN0_MASK);	//L2 cache attribute
	vtcr |= ((MEM_INNER_SHAREABLE << VTCR_SH0_SHIFT) & VTCR_SH0_MASK);	//shareability attribute

	sysreg_write_vtcr(vtcr);

	vtcr = sysreg_read_vtcr();
	uart_puts("VTCR after= ");
	//debug_hexdumpu32(vtcr);

	hdcr = sysreg_read_hdcr();
	uart_puts("HDCR before= ");
	//debug_hexdumpu32(hdcr);

	hdcr &= HDCR_HPMN_MASK;
	sysreg_write_hdcr(hdcr);

	hdcr = sysreg_read_hdcr();
	uart_puts("HDCR after= ");
	//debug_hexdumpu32(hdcr);

	hcptr = sysreg_read_hcptr();
	uart_puts("HCPTR before= ");
	//debug_hexdumpu32(hcptr);

	hcptr = 0;
	hcptr |= HCPTR_RES1_MASK;
	sysreg_write_hcptr(hcptr);

	hcptr = sysreg_read_hcptr();
	uart_puts("HCPTR after= ");
	//debug_hexdumpu32(hcptr);

	hstr = sysreg_read_hstr();
	uart_puts("HSTR before= ");
	//debug_hexdumpu32(hstr);

	sysreg_write_hstr(0);

	hstr = sysreg_read_hstr();
	uart_puts("HSTR after= ");
	//debug_hexdumpu32(hstr);

}

//
// we need the l1 ldesc table to be aligned to 5-VTCR.T0SZ since we use a 3-level
// page table. Since we set VTCR.T0SZ=0 (32-bit physical addressing) we need to
// align at 2**5 which is 32 byte
// c.f. G6.2.162 ARMv8
//
__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 l1_ldesc_table[L1_LDESC_TABLE_MAXENTRIES];

__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 l2_ldesc_table[L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES];
__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 l3_ldesc_table[L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES * L3_LDESC_TABLE_MAXENTRIES];





void s2pgtbl_populate_tables(void){
	u32 i;
	u64 attrs;
	//u64 roattrs;
	u64 attrs_dev;
	u64 attrs_noaccess;

	attrs = (LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_BACK_CACHEABLE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_READ_WRITE << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;

	//attrs = (LDESC_S2_MC_OUTER_NON_CACHEABLE_INNER_NON_CACHEABLE << LDESC_S2_MEMATTR_MC_SHIFT) |
	//		(LDESC_S2_S2AP_READ_WRITE << LDESC_S2_MEMATTR_S2AP_SHIFT) |
	//		(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
	//		LDESC_S2_MEMATTR_AF_MASK;


	attrs_dev = (LDESC_S2_MC_DEVnGnRE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_READ_WRITE << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_NON_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;

	attrs_noaccess = (LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_BACK_CACHEABLE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_NO_ACCESS << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;




	//roattrs = (LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_BACK_CACHEABLE << LDESC_S2_MEMATTR_MC_SHIFT) |
	//		(LDESC_S2_S2AP_READ_ONLY << LDESC_S2_MEMATTR_S2AP_SHIFT) |
	//		(MEM_OUTER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
	//		LDESC_S2_MEMATTR_AF_MASK;


	//debug
	uart_puts(" attrs=\n");
	//debug_hexdumpu32(attrs >> 32);
	//debug_hexdumpu32((u32)attrs);
	//uart_puts(" roattrs=\n");
	////debug_hexdumpu32(roattrs >> 32);
	////debug_hexdumpu32((u32)roattrs);


	//populate l1 ldesc table
	for(i=0; i < L1_LDESC_TABLE_MAXENTRIES; i++){
		if( i < L1_LDESC_TABLE_ENTRIES)
			l1_ldesc_table[i] = ldesc_make_s2_l1e_table((u32)&l2_ldesc_table[i * L2_LDESC_TABLE_MAXENTRIES]);
			//l1_ldesc_table[i] = ldesc_make_s2_l1e_block( (i * PAGE_SIZE_1G), attrs);
		else
			l1_ldesc_table[i] = ldesc_make_s2_l1e_invalid();
	}

	//debug
	uart_puts("L1 LDESC table dump follows:\n");
	for(i=0; i < L1_LDESC_TABLE_ENTRIES; i++){
		//debug_hexdumpu32(l1_ldesc_table[i] >> 32);
		//debug_hexdumpu32((u32)l1_ldesc_table[i]);
	}


	//populate l2 ldesc table
	for(i=0; i < (L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES); i++){
		l2_ldesc_table[i] = ldesc_make_s2_l2e_table((u32)&l3_ldesc_table[i * L3_LDESC_TABLE_MAXENTRIES]);
		//l2_ldesc_table[i] = ldesc_make_s2_l2e_block( (i * PAGE_SIZE_2M), attrs);
	}


	//populate l3 ldesc table
	for(i=0; i < (L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES * L3_LDESC_TABLE_MAXENTRIES); i++){
		//if( (i * PAGE_SIZE_4K) == GUESTOS_TESTPAGE_ADDR)
		//	l3_ldesc_table[i] = ldesc_make_s2_l3e_page((i * PAGE_SIZE_4K), roattrs);
		//else
		//	l3_ldesc_table[i] = ldesc_make_s2_l3e_page((i * PAGE_SIZE_4K), attrs);
		if ( (i * PAGE_SIZE_4K) >= BCM2837_PERIPHERALS_BASE )
			l3_ldesc_table[i] = ldesc_make_s2_l3e_page((i * PAGE_SIZE_4K), attrs_dev);
		else if ( ((i * PAGE_SIZE_4K) >= __UBERSPARK_UOBJCOLL_CONFIGDEF_UXMHF_CORE_START_ADDR__) &&
				  ((i * PAGE_SIZE_4K) < __UBERSPARK_UOBJCOLL_CONFIGDEF_UXMHF_CORE_END_ADDR__) )
			l3_ldesc_table[i] = ldesc_make_s2_l3e_page((i * PAGE_SIZE_4K), attrs_noaccess);
		else
			l3_ldesc_table[i] = ldesc_make_s2_l3e_page((i * PAGE_SIZE_4K), attrs);
	}

}


void s2pgtbl_loadpgtblbase(void){
	u64 vttbr;

	_XDPRINTFSMP_("%s: L1 DESC table at=0x%08x\n", __func__, (u32)&l1_ldesc_table);

	vttbr = sysreg_read_vttbr();
	_XDPRINTFSMP_("%s: VTTBR before=0x%016llx\n", __func__, vttbr);

	//uart_puts("VTTBR before=");
	////debug_hexdumpu32(vttbr >> 32);
	////debug_hexdumpu32((u32)vttbr);

	vttbr = 0;
	vttbr |= ((u64)&l1_ldesc_table & VTTBR_BADDR_MASK);
	vttbr |= (((u64)0x2 << VTTBR_VMID_SHIFT) & VTTBR_VMID_MASK);
	sysreg_write_vttbr(vttbr);


	vttbr = sysreg_read_vttbr();
	_XDPRINTFSMP_("%s: VTTBR after=0x%016llx\n", __func__, vttbr);


	//uart_puts("VTTBR after=");
	////debug_hexdumpu32(vttbr >> 32);
	////debug_hexdumpu32((u32)vttbr);

}

void s2pgtbl_activatetranslation(void){
	u32 hcr;

	hcr = sysreg_read_hcr();
	uart_puts("HCR before=");
	//debug_hexdumpu32(hcr);

	hcr |= HCR_VM_MASK;
	sysreg_write_hcr(hcr);

	hcr = sysreg_read_hcr();
	uart_puts("HCR after=");
	//debug_hexdumpu32(hcr);

}
