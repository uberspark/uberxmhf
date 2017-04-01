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


__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 hyp_l1_ldesc_table[L1_LDESC_TABLE_MAXENTRIES];
__attribute__((section(".paligndata"))) __attribute__((align(PAGE_SIZE_4K))) u64 hyp_l2_ldesc_table[L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES];

void hyppgtbl_populate_tables(void){
	u32 i;

	//populate l1 ldesc table
	for(i=0; i < L1_LDESC_TABLE_MAXENTRIES; i++){
		if( i < L1_LDESC_TABLE_ENTRIES)
			l1_ldesc_table[i] = ldesc_make_s2_l1e_table((u32)&l2_ldesc_table[i * L2_LDESC_TABLE_MAXENTRIES]);
		else
			l1_ldesc_table[i] = ldesc_make_s2_l1e_invalid();
	}



}


