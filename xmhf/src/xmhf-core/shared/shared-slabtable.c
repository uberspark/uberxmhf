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
 * slab table structure that is mapped into every slab memory view
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>

extern u8 _slab_xcprimeon_code_start[];													
extern u8 _slab_xcprimeon_code_end[];														
extern u8 _slab_xcprimeon_rodata_start[];													
extern u8 _slab_xcprimeon_rodata_end[];													
extern u8 _slab_xcprimeon_rwdata_start[];													
extern u8 _slab_xcprimeon_rwdata_end[];													
extern u8 _slab_xcprimeon_stack_start[];													
extern u8 _slab_xcprimeon_stack_end[];														
extern u8 _slab_xcprimeon_entrypoint[];	

extern u8 _slab_testslab_code_start[];													
extern u8 _slab_testslab_code_end[];														
extern u8 _slab_testslab_rodata_start[];													
extern u8 _slab_testslab_rodata_end[];													
extern u8 _slab_testslab_rwdata_start[];													
extern u8 _slab_testslab_rwdata_end[];													
extern u8 _slab_testslab_stack_start[];													
extern u8 _slab_testslab_stack_end[];														
extern u8 _slab_testslab_entrypoint[];	

extern u8 _slab_xcinitbs_code_start[];													
extern u8 _slab_xcinitbs_code_end[];														
extern u8 _slab_xcinitbs_rodata_start[];													
extern u8 _slab_xcinitbs_rodata_end[];													
extern u8 _slab_xcinitbs_rwdata_start[];													
extern u8 _slab_xcinitbs_rwdata_end[];													
extern u8 _slab_xcinitbs_stack_start[];													
extern u8 _slab_xcinitbs_stack_end[];														
extern u8 _slab_xcinitbs_entrypoint[];	

extern u8 _slab_xcinit_code_start[];													
extern u8 _slab_xcinit_code_end[];														
extern u8 _slab_xcinit_rodata_start[];													
extern u8 _slab_xcinit_rodata_end[];													
extern u8 _slab_xcinit_rwdata_start[];													
extern u8 _slab_xcinit_rwdata_end[];													
extern u8 _slab_xcinit_stack_start[];													
extern u8 _slab_xcinit_stack_end[];														
extern u8 _slab_xcinit_entrypoint[];	

extern u8 _slab_xcihub_code_start[];													
extern u8 _slab_xcihub_code_end[];														
extern u8 _slab_xcihub_rodata_start[];													
extern u8 _slab_xcihub_rodata_end[];													
extern u8 _slab_xcihub_rwdata_start[];													
extern u8 _slab_xcihub_rwdata_end[];													
extern u8 _slab_xcihub_stack_start[];													
extern u8 _slab_xcihub_stack_end[];														
extern u8 _slab_xcihub_entrypoint[];	

extern u8 _slab_xccoreapi_code_start[];													
extern u8 _slab_xccoreapi_code_end[];														
extern u8 _slab_xccoreapi_rodata_start[];													
extern u8 _slab_xccoreapi_rodata_end[];													
extern u8 _slab_xccoreapi_rwdata_start[];													
extern u8 _slab_xccoreapi_rwdata_end[];													
extern u8 _slab_xccoreapi_stack_start[];													
extern u8 _slab_xccoreapi_stack_end[];														
extern u8 _slab_xccoreapi_entrypoint[];	

extern u8 _slab_xcexhub_code_start[];													
extern u8 _slab_xcexhub_code_end[];														
extern u8 _slab_xcexhub_rodata_start[];													
extern u8 _slab_xcexhub_rodata_end[];													
extern u8 _slab_xcexhub_rwdata_start[];													
extern u8 _slab_xcexhub_rwdata_end[];													
extern u8 _slab_xcexhub_stack_start[];													
extern u8 _slab_xcexhub_stack_end[];														
extern u8 _slab_xcexhub_entrypoint[];	

extern u8 _slab_xhhyperdep_code_start[];													
extern u8 _slab_xhhyperdep_code_end[];														
extern u8 _slab_xhhyperdep_rodata_start[];													
extern u8 _slab_xhhyperdep_rodata_end[];													
extern u8 _slab_xhhyperdep_rwdata_start[];													
extern u8 _slab_xhhyperdep_rwdata_end[];													
extern u8 _slab_xhhyperdep_stack_start[];													
extern u8 _slab_xhhyperdep_stack_end[];														
extern u8 _slab_xhhyperdep_entrypoint[];	

__attribute__ ((section(".sharedro_slab_table"))) slab_header_t _slab_table[XMHF_SLAB_NUMBEROFSLABS] = {			
	{	
		.slab_index = 0,															
		.slab_macmid = 0,															
		.slab_privilegemask = 0,													
		.slab_tos = _slab_xcprimeon_stack_end, 					
		.slab_code.start = _slab_xcprimeon_code_start,									
		.slab_code.end = _slab_xcprimeon_code_end,										
		.slab_rodata.start = _slab_xcprimeon_rodata_start,									
		.slab_rodata.end = _slab_xcprimeon_rodata_end,									
		.slab_rwdata.start = _slab_xcprimeon_rwdata_start,									
		.slab_rwdata.end = _slab_xcprimeon_rwdata_end,									
		.slab_stack.start = _slab_xcprimeon_stack_start,									
		.slab_stack.end = _slab_xcprimeon_stack_end,
		.entry_cr3 = _slab_xcprimeon_entrypoint,												
	},


	{	
		.slab_index = 0,															
		.slab_macmid = 0,															
		.slab_privilegemask = 0,													
		.slab_tos = _slab_testslab_stack_end, 					
		.slab_code.start = _slab_testslab_code_start,									
		.slab_code.end = _slab_testslab_code_end,										
		.slab_rodata.start = _slab_testslab_rodata_start,									
		.slab_rodata.end = _slab_testslab_rodata_end,									
		.slab_rwdata.start = _slab_testslab_rwdata_start,									
		.slab_rwdata.end = _slab_testslab_rwdata_end,									
		.slab_stack.start = _slab_testslab_stack_start,									
		.slab_stack.end = _slab_testslab_stack_end,
		.entry_cr3 = _slab_testslab_entrypoint,												
	},

	{	
		.slab_index = 0,															
		.slab_macmid = 0,															
		.slab_privilegemask = 0,													
		.slab_tos = _slab_xcinitbs_stack_end, 					
		.slab_code.start = _slab_xcinitbs_code_start,									
		.slab_code.end = _slab_xcinitbs_code_end,										
		.slab_rodata.start = _slab_xcinitbs_rodata_start,									
		.slab_rodata.end = _slab_xcinitbs_rodata_end,									
		.slab_rwdata.start = _slab_xcinitbs_rwdata_start,									
		.slab_rwdata.end = _slab_xcinitbs_rwdata_end,									
		.slab_stack.start = _slab_xcinitbs_stack_start,									
		.slab_stack.end = _slab_xcinitbs_stack_end,
		.entry_cr3 = _slab_xcinitbs_entrypoint,												
	},

	{	
		.slab_index = 0,															
		.slab_macmid = 0,															
		.slab_privilegemask = 0,													
		.slab_tos = _slab_xcinit_stack_end, 					
		.slab_code.start = _slab_xcinit_code_start,									
		.slab_code.end = _slab_xcinit_code_end,										
		.slab_rodata.start = _slab_xcinit_rodata_start,									
		.slab_rodata.end = _slab_xcinit_rodata_end,									
		.slab_rwdata.start = _slab_xcinit_rwdata_start,									
		.slab_rwdata.end = _slab_xcinit_rwdata_end,									
		.slab_stack.start = _slab_xcinit_stack_start,									
		.slab_stack.end = _slab_xcinit_stack_end,
		.entry_cr3 = _slab_xcinit_entrypoint,												
	},

	{	
		.slab_index = 0,															
		.slab_macmid = 0,															
		.slab_privilegemask = 0,													
		.slab_tos = _slab_xcihub_stack_end, 					
		.slab_code.start = _slab_xcihub_code_start,									
		.slab_code.end = _slab_xcihub_code_end,										
		.slab_rodata.start = _slab_xcihub_rodata_start,									
		.slab_rodata.end = _slab_xcihub_rodata_end,									
		.slab_rwdata.start = _slab_xcihub_rwdata_start,									
		.slab_rwdata.end = _slab_xcihub_rwdata_end,									
		.slab_stack.start = _slab_xcihub_stack_start,									
		.slab_stack.end = _slab_xcihub_stack_end,
		.entry_cr3 = _slab_xcihub_entrypoint,												
	},

	{	
		.slab_index = 0,															
		.slab_macmid = 0,															
		.slab_privilegemask = 0,													
		.slab_tos = _slab_xccoreapi_stack_end, 					
		.slab_code.start = _slab_xccoreapi_code_start,									
		.slab_code.end = _slab_xccoreapi_code_end,										
		.slab_rodata.start = _slab_xccoreapi_rodata_start,									
		.slab_rodata.end = _slab_xccoreapi_rodata_end,									
		.slab_rwdata.start = _slab_xccoreapi_rwdata_start,									
		.slab_rwdata.end = _slab_xccoreapi_rwdata_end,									
		.slab_stack.start = _slab_xccoreapi_stack_start,									
		.slab_stack.end = _slab_xccoreapi_stack_end,
		.entry_cr3 = _slab_xccoreapi_entrypoint,												
	},

	{	
		.slab_index = 0,															
		.slab_macmid = 0,															
		.slab_privilegemask = 0,													
		.slab_tos = _slab_xcexhub_stack_end, 					
		.slab_code.start = _slab_xcexhub_code_start,									
		.slab_code.end = _slab_xcexhub_code_end,										
		.slab_rodata.start = _slab_xcexhub_rodata_start,									
		.slab_rodata.end = _slab_xcexhub_rodata_end,									
		.slab_rwdata.start = _slab_xcexhub_rwdata_start,									
		.slab_rwdata.end = _slab_xcexhub_rwdata_end,									
		.slab_stack.start = _slab_xcexhub_stack_start,									
		.slab_stack.end = _slab_xcexhub_stack_end,
		.entry_cr3 = _slab_xcexhub_entrypoint,												
	},

	{	
		.slab_index = 0,															
		.slab_macmid = 0,															
		.slab_privilegemask = 0,													
		.slab_tos = _slab_xhhyperdep_stack_end, 					
		.slab_code.start = _slab_xhhyperdep_code_start,									
		.slab_code.end = _slab_xhhyperdep_code_end,										
		.slab_rodata.start = _slab_xhhyperdep_rodata_start,									
		.slab_rodata.end = _slab_xhhyperdep_rodata_end,									
		.slab_rwdata.start = _slab_xhhyperdep_rwdata_start,									
		.slab_rwdata.end = _slab_xhhyperdep_rwdata_end,									
		.slab_stack.start = _slab_xhhyperdep_stack_start,									
		.slab_stack.end = _slab_xhhyperdep_stack_end,
		.entry_cr3 = _slab_xhhyperdep_entrypoint,												
	},

};																				






