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





