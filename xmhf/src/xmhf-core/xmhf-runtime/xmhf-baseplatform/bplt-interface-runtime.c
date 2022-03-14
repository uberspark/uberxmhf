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

/*
 * EMHF base platform component interface
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

extern RPB *rpb;
// extern GRUBE820 g_e820map[];

// Traverse the E820 map and return the base and limit of used system physical address (i.e., used by main memory and MMIO).
// [NOTE] <machine_high_spa> must be u64 even on 32-bit machines, because it could be 4G, and hence overflow u32.
// Return: <machine_base_spa> and <machine_limit_spa> may not be 4K-aligned.
// [TODO][Issue 85] Move this function to a better place
bool xmhf_baseplatform_x86_e820_paddr_range(spa_t* machine_base_spa, u64* machine_limit_spa)
{
	u32 i = 0;
	spa_t base_spa = INVALID_SPADDR;
	u64 limit_spa = INVALID_SPADDR;

	// Sanity checks
	if(!machine_base_spa || !machine_limit_spa)
		return false;

	if(!rpb)
		return false;

	if(!rpb->XtVmmE820NumEntries)
		return false;

	// Traverse E820 entries to find the base and limit of the system phsical address.
	// Note: E820 entries are unsorted, and sometimes overlapping with each other.
	// Note: We ignore the type of E820 entries.
	// see https://wiki.osdev.org/Detecting_Memory_(x86)#BIOS_Function:_INT_0x15.2C_EAX_.3D_0xE820
	base_spa = UINT32sToSPADDR(g_e820map[0].baseaddr_high, g_e820map[0].baseaddr_low);
	FOREACH_S(i, rpb->XtVmmE820NumEntries, MAX_E820_ENTRIES, 0, 1)
	{
		spa_t cur_base_spa = UINT32sToSPADDR(g_e820map[i].baseaddr_high, g_e820map[i].baseaddr_low);
		size_t cur_size = UINT32sToSIZE(g_e820map[i].length_high, g_e820map[i].length_low);
		u64 cur_limit_spa = (spa_t)(cur_base_spa + cur_size);

		if(cur_base_spa <= base_spa)
		{
			// Found a lower base
			base_spa = cur_base_spa;
		}

		if(cur_limit_spa >= limit_spa)
		{
			// Found an upper limit
			limit_spa = cur_limit_spa;
		}
	}

	*machine_base_spa = base_spa;
	*machine_limit_spa = limit_spa;

	return true;
}
