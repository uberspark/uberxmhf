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
	uxmhf-rpi3 image linker script

	author: amit vasudevan (amitvasudevan@acm.org)
*/
#include <config.h>

ENTRY(entry)

MEMORY
{
	ram (rwxai) : ORIGIN = UXMHF_CORE_START_ADDR, LENGTH = UXMHF_CORE_SIZE
	unaccounted (rwxai) : ORIGIN = 0, LENGTH = 0 /* see section .unaccounted at end */
}

SECTIONS
{
	. = UXMHF_CORE_START_ADDR;
    
    .text : { 
    	*(.text) 
    } > ram = 0x0000

    .data : { 
    	*(.rodata) 
    	*(.data)
    	*(.bss) 
		. = ALIGN(0x4000);
    	*(.paligndata) 
    	. = ALIGN(0x200000);
    	*(.palign2mdata)
	} > ram = 0x0000

    
    .stack : { 
    	*(.stack)
		. = ALIGN(0x200000);
	} > ram = 0x0000

	/DISCARD/ : {
		*(.ARM.attributes)
		*(.comment)
		*(.ARM.extab)
		*(.ARM.exidx)
		*(.debug_*)
	}

	/* this is to cause the link to fail if there is
	* anything we didn't explicitly place.
	* when this does cause link to fail, temporarily comment
	* this part out to see what sections end up in the output
	* which are not handled above, and handle them.
	*/
	.unaccounted : {
	*(*)
	} >unaccounted
	
}

