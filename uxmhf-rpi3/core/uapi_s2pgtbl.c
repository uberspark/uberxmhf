/*
	ARM 8 stage-2 page table translation uapi

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>
#include <guestos.h>

extern u64 l3_ldesc_table[L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES * L3_LDESC_TABLE_MAXENTRIES];

void uapi_s2pgtbl_setprot(u32 address, u64 protection){
	u32 index;

	if ( !((address >= UXMHF_CORE_START_ADDR) &&
			  (address < UXMHF_CORE_END_ADDR)) ){
		index = address/PAGE_SIZE_4K;
		l3_ldesc_table[index] = ldesc_make_s2_l3e_page(address, protection);
	}

}

u64 uapi_s2pgtbl_getprot(u32 address){
	u32 index;
	u64 result=0;

	if ( !((address >= UXMHF_CORE_START_ADDR) &&
			  (address < UXMHF_CORE_END_ADDR)) ){
		index = address/PAGE_SIZE_4K;
		result = l3_ldesc_table[index];
	}else{
		result=0;
	}

	return result;
}


