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

// XMHF core initialization boostrap (init-bs) entry module
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <xmhf-core.h> 
#include <xmhf-slab-implib.h>

extern slab_table_t _slab_table[];

void xmhf_runtime_entry(void){

	//setup debugging	
	xmhf_debug_init((char *)&xcbootinfo->debugcontrol_buffer);
	printf("\nxmhf-core: starting...");

    //[debug] dump E820
 	#ifndef __XMHF_VERIFICATION__
 	printf("\nNumber of E820 entries = %u", xcbootinfo->memmapinfo_numentries);
	{
		int i;
		for(i=0; i < (int)xcbootinfo->memmapinfo_numentries; i++){
			printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
			  xcbootinfo->memmapinfo_buffer[i].baseaddr_high, xcbootinfo->memmapinfo_buffer[i].baseaddr_low,
			  xcbootinfo->memmapinfo_buffer[i].length_high, xcbootinfo->memmapinfo_buffer[i].length_low,
			  xcbootinfo->memmapinfo_buffer[i].type);
		}
  	}
	#endif //__XMHF_VERIFICATION__

  	//initialize basic platform elements
	xmhf_baseplatform_initialize();

	//setup XMHF exception handler component
	xmhf_xcphandler_initialize();

	#if defined (__DMAP__)
	xmhf_dmaprot_reinitialize();
	#endif

	//initialize richguest
	//xmhf_richguest_initialize();


	//[test] slab
	{
			extern slab_header_t _test_slab_header;
			context_desc_t ctx;
			u32 value;
			
			printf("\nslab testing, dumping slab header");
			printf("\n	slab_index=%u", _test_slab_header.slab_index);
			printf("\n	slab_macmid=%08x", _test_slab_header.slab_macmid);
			printf("\n	slab_privilegemask=%08x", _test_slab_header.slab_privilegemask);
			printf("\n	slab_tos=%08x", _test_slab_header.slab_tos);
			printf("\n  slab_rodata(%08x-%08x)", _test_slab_header.slab_rodata.start, _test_slab_header.slab_rodata.end);
			printf("\n  slab_rwdata(%08x-%08x)", _test_slab_header.slab_rwdata.start, _test_slab_header.slab_rwdata.end);
			printf("\n  slab_code(%08x-%08x)", _test_slab_header.slab_code.start, _test_slab_header.slab_code.end);
			printf("\n  slab_stack(%08x-%08x)", _test_slab_header.slab_stack.start, _test_slab_header.slab_stack.end);
			printf("\n  slab_trampoline(%08x-%08x)", _test_slab_header.slab_trampoline.start, _test_slab_header.slab_trampoline.end);
			printf("\n  slab_entrycr3=%08x", _test_slab_header.entry_cr3);
			
			_slab_table[0].slab_header.entry_cr3 = _test_slab_header.entry_cr3;

			//invoke slab interface
			printf("\n%s: preparing to invoke slab interfaces", __FUNCTION__);
			entry_0();
			value=entry_1(5, 3);
			ctx= entry_2(2048, true, 4096);
			printf("\n%s: came back to initbs, value=%u", __FUNCTION__, value);
			printf("\n%s: ctx: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, ctx.cpu_desc.cpu_index, ctx.cpu_desc.isbsp, ctx.partition_desc.partition_index);

	}



	//invoke XMHF api hub initialization function to initialize core API
	//interface layer
	xmhf_apihub_initialize();

	//initialize base platform with SMP 
	xmhf_baseplatform_smpinitialize();

	printf("\nRuntime: We should NEVER get here!");
	HALT_ON_ERRORCOND(0);
}

