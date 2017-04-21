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



