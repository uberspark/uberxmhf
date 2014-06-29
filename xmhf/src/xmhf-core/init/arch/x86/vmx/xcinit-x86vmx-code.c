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

// XMHF rich guest -- initialization portion, x86 (VMX) backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf-core.h> 
#include <xc-x86.h>
#include <xc-x86vmx.h>

#include <xc-init.h>

#define __XMHF_SLAB_CALLER_INDEX__	XMHF_SLAB_INIT_INDEX
#include <xc-coreapi.h>
#undef __XMHF_SLAB_CALLER_INDEX__


static struct _memorytype _vmx_ept_memorytypes[MAX_MEMORYTYPE_ENTRIES]; //EPT memory types array

//----------------------------------------------------------------------
// local (static) support function forward declarations
static void _vmx_gathermemorytypes(void);
static u32 _vmx_getmemorytypeforphysicalpage(u64 pagebaseaddr);
//static void _vmx_setupEPT(xc_partition_hptdata_x86vmx_t *eptdata);
static void _vmx_setupEPT(context_desc_t context_desc);

//---gather memory types for system physical memory------------------------------
static void _vmx_gathermemorytypes(void){
 	u32 eax, ebx, ecx, edx;
	u32 index=0;
	u32 num_vmtrrs=0;	//number of variable length MTRRs supported by the CPU
  
	//0. sanity check
  	//check MTRR support
  	eax=0x00000001;
  	ecx=0x00000000;
	#ifndef __XMHF_VERIFICATION__
  	asm volatile ("cpuid\r\n"
            :"=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
            :"a"(eax), "c" (ecx));
  	#endif
  	
  	if( !(edx & (u32)(1 << 12)) ){
  		printf("\n%s: CPU does not support MTRRs!", __FUNCTION__);
  		HALT();
  	}

  	//check MTRR caps
  	rdmsr(IA32_MTRRCAP, &eax, &edx);
	num_vmtrrs = (u8)eax;
  	printf("\nIA32_MTRRCAP: VCNT=%u, FIX=%u, WC=%u, SMRR=%u",
  		num_vmtrrs, ((eax & (1 << 8)) >> 8),  ((eax & (1 << 10)) >> 10),
  			((eax & (1 << 11)) >> 11));
	//sanity check that fixed MTRRs are supported
  	HALT_ON_ERRORCOND( ((eax & (1 << 8)) >> 8) );
  	//ensure number of variable MTRRs are within the maximum supported
  	HALT_ON_ERRORCOND( (num_vmtrrs <= MAX_VARIABLE_MEMORYTYPE_ENTRIES) );
  	

	#ifndef __XMHF_VERIFICATION__
	//1. clear memorytypes array
	memset((void *)&_vmx_ept_memorytypes, 0, sizeof(struct _memorytype) * MAX_MEMORYTYPE_ENTRIES);
	#endif

	//2. grab memory types using FIXED MTRRs
    //0x00000000-0x0007FFFF
    rdmsr(IA32_MTRR_FIX64K_00000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x00000000; _vmx_ept_memorytypes[index].endaddr = 0x0000FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00010000; _vmx_ept_memorytypes[index].endaddr = 0x0001FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00020000; _vmx_ept_memorytypes[index].endaddr = 0x0002FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x00030000; _vmx_ept_memorytypes[index].endaddr = 0x0003FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x00040000; _vmx_ept_memorytypes[index].endaddr = 0x0004FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00050000; _vmx_ept_memorytypes[index].endaddr = 0x0005FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00060000; _vmx_ept_memorytypes[index].endaddr = 0x0006FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x00070000; _vmx_ept_memorytypes[index].endaddr = 0x0007FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x00080000-0x0009FFFF
  	rdmsr(IA32_MTRR_FIX16K_80000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x00080000; _vmx_ept_memorytypes[index].endaddr = 0x00083FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00084000; _vmx_ept_memorytypes[index].endaddr = 0x00087FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00088000; _vmx_ept_memorytypes[index].endaddr = 0x0008BFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x0008C000; _vmx_ept_memorytypes[index].endaddr = 0x0008FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x00090000; _vmx_ept_memorytypes[index].endaddr = 0x00093FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00094000; _vmx_ept_memorytypes[index].endaddr = 0x00097FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00098000; _vmx_ept_memorytypes[index].endaddr = 0x0009BFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x0009C000; _vmx_ept_memorytypes[index].endaddr = 0x0009FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000A0000-0x000BFFFF
	  rdmsr(IA32_MTRR_FIX16K_A0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000A0000; _vmx_ept_memorytypes[index].endaddr = 0x000A3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000A4000; _vmx_ept_memorytypes[index].endaddr = 0x000A7FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000A8000; _vmx_ept_memorytypes[index].endaddr = 0x000ABFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000AC000; _vmx_ept_memorytypes[index].endaddr = 0x000AFFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000B0000; _vmx_ept_memorytypes[index].endaddr = 0x000B3FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000B4000; _vmx_ept_memorytypes[index].endaddr = 0x000B7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000B8000; _vmx_ept_memorytypes[index].endaddr = 0x000BBFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000BC000; _vmx_ept_memorytypes[index].endaddr = 0x000BFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C0000-0x000C7FFF
    rdmsr(IA32_MTRR_FIX4K_C0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000C0000; _vmx_ept_memorytypes[index].endaddr = 0x000C0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C1000; _vmx_ept_memorytypes[index].endaddr = 0x000C1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000C2000; _vmx_ept_memorytypes[index].endaddr = 0x000C2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000C3000; _vmx_ept_memorytypes[index].endaddr = 0x000C3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000C4000; _vmx_ept_memorytypes[index].endaddr = 0x000C4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C5000; _vmx_ept_memorytypes[index].endaddr = 0x000C5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000C6000; _vmx_ept_memorytypes[index].endaddr = 0x000C6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000C7000; _vmx_ept_memorytypes[index].endaddr = 0x000C7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C8000-0x000C8FFF
	  rdmsr(IA32_MTRR_FIX4K_C8000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000C8000; _vmx_ept_memorytypes[index].endaddr = 0x000C8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C9000; _vmx_ept_memorytypes[index].endaddr = 0x000C9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000CA000; _vmx_ept_memorytypes[index].endaddr = 0x000CAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000CB000; _vmx_ept_memorytypes[index].endaddr = 0x000CBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000CC000; _vmx_ept_memorytypes[index].endaddr = 0x000CCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000CD000; _vmx_ept_memorytypes[index].endaddr = 0x000CDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000CE000; _vmx_ept_memorytypes[index].endaddr = 0x000CEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000CF000; _vmx_ept_memorytypes[index].endaddr = 0x000CFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D0000-0x000D7FFF
    rdmsr(IA32_MTRR_FIX4K_D0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000D0000; _vmx_ept_memorytypes[index].endaddr = 0x000D0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D1000; _vmx_ept_memorytypes[index].endaddr = 0x000D1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000D2000; _vmx_ept_memorytypes[index].endaddr = 0x000D2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000D3000; _vmx_ept_memorytypes[index].endaddr = 0x000D3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000D4000; _vmx_ept_memorytypes[index].endaddr = 0x000D4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D5000; _vmx_ept_memorytypes[index].endaddr = 0x000D5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000D6000; _vmx_ept_memorytypes[index].endaddr = 0x000D6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000D7000; _vmx_ept_memorytypes[index].endaddr = 0x000D7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D8000-0x000DFFFF
  	rdmsr(IA32_MTRR_FIX4K_D8000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000D8000; _vmx_ept_memorytypes[index].endaddr = 0x000D8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D9000; _vmx_ept_memorytypes[index].endaddr = 0x000D9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000DA000; _vmx_ept_memorytypes[index].endaddr = 0x000DAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000DB000; _vmx_ept_memorytypes[index].endaddr = 0x000DBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000DC000; _vmx_ept_memorytypes[index].endaddr = 0x000DCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000DD000; _vmx_ept_memorytypes[index].endaddr = 0x000DDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000DE000; _vmx_ept_memorytypes[index].endaddr = 0x000DEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000DF000; _vmx_ept_memorytypes[index].endaddr = 0x000DFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E0000-0x000E7FFF
    rdmsr(IA32_MTRR_FIX4K_E0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000E0000; _vmx_ept_memorytypes[index].endaddr = 0x000E0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E1000; _vmx_ept_memorytypes[index].endaddr = 0x000E1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000E2000; _vmx_ept_memorytypes[index].endaddr = 0x000E2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000E3000; _vmx_ept_memorytypes[index].endaddr = 0x000E3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000E4000; _vmx_ept_memorytypes[index].endaddr = 0x000E4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E5000; _vmx_ept_memorytypes[index].endaddr = 0x000E5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000E6000; _vmx_ept_memorytypes[index].endaddr = 0x000E6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000E7000; _vmx_ept_memorytypes[index].endaddr = 0x000E7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E8000-0x000EFFFF
	  rdmsr(IA32_MTRR_FIX4K_E8000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000E8000; _vmx_ept_memorytypes[index].endaddr = 0x000E8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E9000; _vmx_ept_memorytypes[index].endaddr = 0x000E9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000EA000; _vmx_ept_memorytypes[index].endaddr = 0x000EAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000EB000; _vmx_ept_memorytypes[index].endaddr = 0x000EBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000EC000; _vmx_ept_memorytypes[index].endaddr = 0x000ECFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000ED000; _vmx_ept_memorytypes[index].endaddr = 0x000EDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000EE000; _vmx_ept_memorytypes[index].endaddr = 0x000EEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000EF000; _vmx_ept_memorytypes[index].endaddr = 0x000EFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F0000-0x000F7FFF
  	rdmsr(IA32_MTRR_FIX4K_F0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000F0000; _vmx_ept_memorytypes[index].endaddr = 0x000F0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F1000; _vmx_ept_memorytypes[index].endaddr = 0x000F1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000F2000; _vmx_ept_memorytypes[index].endaddr = 0x000F2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000F3000; _vmx_ept_memorytypes[index].endaddr = 0x000F3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000F4000; _vmx_ept_memorytypes[index].endaddr = 0x000F4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F5000; _vmx_ept_memorytypes[index].endaddr = 0x000F5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000F6000; _vmx_ept_memorytypes[index].endaddr = 0x000F6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000F7000; _vmx_ept_memorytypes[index].endaddr = 0x000F7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F8000-0x000FFFFF
  	rdmsr(IA32_MTRR_FIX4K_F8000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000F8000; _vmx_ept_memorytypes[index].endaddr = 0x000F8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F9000; _vmx_ept_memorytypes[index].endaddr = 0x000F9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000FA000; _vmx_ept_memorytypes[index].endaddr = 0x000FAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000FB000; _vmx_ept_memorytypes[index].endaddr = 0x000FBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000FC000; _vmx_ept_memorytypes[index].endaddr = 0x000FCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000FD000; _vmx_ept_memorytypes[index].endaddr = 0x000FDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000FE000; _vmx_ept_memorytypes[index].endaddr = 0x000FEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000FF000; _vmx_ept_memorytypes[index].endaddr = 0x000FFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);

	       
	//3. grab memory types using variable length MTRRs  
	{
		u64 paddrmask = 0x0000000FFFFFFFFFULL; //36-bits physical address, TODO: need to make this dynamic
		u64 vMTRR_base, vMTRR_mask;
		u32 msrval=IA32_MTRR_PHYSBASE0;
		u32 i;

		for(i=0; i < num_vmtrrs; i++){
			rdmsr(msrval, &eax, &edx);
			vMTRR_base = ((u64)edx << 32) | (u64)eax;
			msrval++;
			rdmsr(msrval, &eax, &edx);
			vMTRR_mask = ((u64)edx << 32) | (u64)eax;
			msrval++;
			if( (vMTRR_mask & ((u64)1 << 11)) ){
				_vmx_ept_memorytypes[index].startaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL);
				_vmx_ept_memorytypes[index].endaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL) + 
					(u64) (~(vMTRR_mask & (u64)0xFFFFFFFFFFFFF000ULL) &
						paddrmask);
				_vmx_ept_memorytypes[index++].type = ((u32)vMTRR_base & (u32)0x000000FF);       
			}else{
				_vmx_ept_memorytypes[index++].invalid = 1;
			}
		}
	}

	printf("\n%s: gathered MTRR details, number of entries=%u", __FUNCTION__, index);
	HALT_ON_ERRORCOND( index <= (MAX_MEMORYTYPE_ENTRIES+1) );

  //[debug: dump the contents of _vmx_ept_memorytypes]
  //{
  //  int i;
  //  for(i=0; i < MAX_MEMORYTYPE_ENTRIES; i++){
  //    printf("\nrange  0x%016llx-0x%016llx (type=%u)", 
  //      _vmx_ept_memorytypes[i].startaddr, _vmx_ept_memorytypes[i].endaddr, _vmx_ept_memorytypes[i].type);
  //  }
  //}

  
}

//---get memory type for a given physical page address--------------------------
//
//11.11.4.1 MTRR Precedences
//  0. if MTRRs are not enabled --> MTRR_TYPE_UC
//  if enabled then
     //if physaddr < 1MB use fixed MTRR ranges return type
     //else if within a valid variable range MTRR then
        //if a single match, return type
        //if two or more and one is UC, return UC
        //if two or more and WB and WT, return WT
        //else invalid combination
     //else
       // return default memory type
//
static u32 _vmx_getmemorytypeforphysicalpage(u64 pagebaseaddr){
 int i;
 u32 prev_type= MTRR_TYPE_RESV; 

  //check if page base address under 1M, if so used FIXED MTRRs
  if(pagebaseaddr < (1024*1024)){
    for(i=0; i < MAX_FIXED_MEMORYTYPE_ENTRIES; i++){
      if( pagebaseaddr >= _vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= _vmx_ept_memorytypes[i].endaddr )
        return _vmx_ept_memorytypes[i].type;    
    }
    
    printf("\n%s: endaddr < 1M and unmatched fixed MTRR. Halt!", __FUNCTION__);
    HALT();
  }
 
  //page base address is above 1M, use VARIABLE MTRRs
  for(i= MAX_FIXED_MEMORYTYPE_ENTRIES; i < MAX_MEMORYTYPE_ENTRIES; i++){
    if( pagebaseaddr >= _vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= _vmx_ept_memorytypes[i].endaddr && 
          (!_vmx_ept_memorytypes[i].invalid) ){
       if(_vmx_ept_memorytypes[i].type == MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_UC;
       }else if(_vmx_ept_memorytypes[i].type == MTRR_TYPE_WT && prev_type != MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_WT;
       }else{
        if(prev_type != MTRR_TYPE_UC && prev_type != MTRR_TYPE_WT){
          if(prev_type == MTRR_TYPE_RESV){
            prev_type = _vmx_ept_memorytypes[i].type;
          }else{
            printf("\nprev_type=%u, _vmx_ept_memorytypes=%u", prev_type, _vmx_ept_memorytypes[i].type);
            HALT_ON_ERRORCOND ( prev_type == _vmx_ept_memorytypes[i].type);
          }
        }
       }        
    }
  }
 
  if(prev_type == MTRR_TYPE_RESV)
    prev_type = MTRR_TYPE_WB; //todo: need to dynamically get the default MTRR (usually WB)
 
  return prev_type;
}


//---setup EPT for VMX----------------------------------------------------------
//static void _vmx_setupEPT(xc_cpu_t *xc_cpu){
//static void _vmx_setupEPT(xc_partition_hptdata_x86vmx_t *eptdata){
static void _vmx_setupEPT(context_desc_t context_desc){
	u64 p_table_value;
	u64 gpa;

	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_4K){
		u32 memorytype = _vmx_getmemorytypeforphysicalpage((u64)gpa);
		//make XMHF physical pages inaccessible
		if( (gpa >= (xcbootinfo->physmem_base)) &&
			(gpa < (xcbootinfo->physmem_base + xcbootinfo->size)) ){
			p_table_value = (u64) (gpa)  | ((u64)memorytype << 3) | (u64)0x0 ;	//not-present
		}else{
			if(memorytype == 0)
				p_table_value = (u64) (gpa)  | ((u64)memorytype << 3) |  (u64)0x7 ;	//present, UC
			else
				p_table_value = (u64) (gpa)  | ((u64)6 << 3) | (u64)0x7 ;	//present, WB, track host MTRR
		}

		//printf("\n%s: gpa=%x, proceedig to call xc_api_hpt_setentry (esp=%x)\n", __FUNCTION__, (u32)gpa, read_esp());
		xc_api_hpt_setentry(context_desc, gpa, p_table_value);
		//printf("\n%s: back, esp=%x\n", __FUNCTION__, read_esp());
	}
}

//---vmx int 15 hook enabling function------------------------------------------
static void	_vmx_int15_initializehook(void){
		//implant VMCALL followed by IRET at 0040:04AC
		xmhfhw_sysmemaccess_writeu8(0x4ac, 0x0f); //VMCALL
		xmhfhw_sysmemaccess_writeu8(0x4ad, 0x01);
		xmhfhw_sysmemaccess_writeu8(0x4ae, 0xc1);
		xmhfhw_sysmemaccess_writeu8(0x4af, 0xcf); //IRET

		//store original INT 15h handler CS:IP following VMCALL and IRET
		xmhfhw_sysmemaccess_writeu16(0x4b0, xmhfhw_sysmemaccess_readu16(0x54)); //original INT 15h IP
		xmhfhw_sysmemaccess_writeu16(0x4b2, xmhfhw_sysmemaccess_readu16(0x56)); //original INT 15h CS
		
		//point IVT INT15 handler to the VMCALL instruction
		xmhfhw_sysmemaccess_writeu16(0x54, 0x00ac); 
		xmhfhw_sysmemaccess_writeu16(0x56, 0x0040); 
}

//-------------------------------------------------------------------------
void xmhf_richguest_arch_initialize(u32 partition_index){
	//xc_partition_t *xc_partition_richguest = &g_xc_primary_partition[partition_index];
	
	//g_xc_primary_partition[XC_PARTITION_RICHGUEST_INDEX].partitionid=XC_PARTITION_RICHGUEST_INDEX;
	//g_xc_primary_partition[XC_PARTITION_RICHGUEST_INDEX].partitiontype = XC_PARTITION_PRIMARY;
	//g_xc_primary_partition[XC_PARTITION_RICHGUEST_INDEX].numcpus = 0;
	context_desc_t context_desc;
	
	context_desc.cpu_desc.cpu_index=XC_PARTITION_INDEX_INVALID;
	context_desc.cpu_desc.isbsp = true;
	context_desc.partition_desc.partition_index = partition_index;


	printf("\n%s: copying boot-module to boot guest: base=%08x, size=%u bytes", __FUNCTION__, (u32)xcbootinfo->richguest_bootmodule_base, xcbootinfo->richguest_bootmodule_size);
	memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)xcbootinfo->richguest_bootmodule_base, xcbootinfo->richguest_bootmodule_size);
		
	printf("\n%s: BSP initializing HPT", __FUNCTION__);
	_vmx_gathermemorytypes();
	//_vmx_setupEPT((xc_partition_hptdata_x86vmx_t *)xc_partition_richguest->hptdata);

	_vmx_setupEPT(context_desc);

	//INT 15h E820 hook enablement for VMX unrestricted guest mode
	//note: this only happens for the BSP
	printf("\n%s: BSP initializing INT 15 hook for UG mode...", __FUNCTION__);
	_vmx_int15_initializehook();
}




//setup guest OS state for the partition
void xmhf_richguest_arch_setupguestOSstate(context_desc_t context_desc){
	xc_hypapp_arch_param_t ap;
	
	//--------------------------------------------------------------------------------------------------------------------------------
	//setup guest state
	//CR0, real-mode, PE and PG bits cleared
	ap = xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS);
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS;
	ap.param.controlregs.cr0 = ap.param.controlregs.cr0 & ~(CR0_PE) & ~(CR0_PG);
	ap.param.controlregs.cr3 = 0;
	xc_api_cpustate_set(context_desc, ap);
	
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS;
	ap.param.cpugprs.eax = 0;
	ap.param.cpugprs.ebx = 0;
	ap.param.cpugprs.ecx = 0;
	ap.param.cpugprs.edx = 0x80;
	ap.param.cpugprs.esi = 0;
	ap.param.cpugprs.edi = 0;
	ap.param.cpugprs.ebp = 0;
	ap.param.cpugprs.esp = 0;
	xc_api_cpustate_set(context_desc, ap);
							

	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
	ap.param.activity.rflags = ((((0 & ~((1<<3)|(1<<5)|(1<<15)) ) | (1 <<1)) | (1<<9)) & ~(1<<14));
	if(context_desc.cpu_desc.isbsp){
		ap.param.activity.rip = 0x7c00;
		ap.param.activity.activity_state = 0;	//normal activity state
	}else{
		ap.param.activity.rip = 0;
		ap.param.activity.activity_state = 3;	//wait-for-SIPI
	}
	ap.param.activity.interruptibility=0;
	xc_api_cpustate_set(context_desc, ap);

	
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC;
	//CS, DS, ES, FS, GS and SS segments
	ap.param.desc.cs.selector 		 = 0  ;
	ap.param.desc.cs.base 			 = 0  ;
	ap.param.desc.cs.limit 			 = 0xFFFF  ;
	ap.param.desc.cs.access_rights 	 = 0x93  ;	
	ap.param.desc.ds.selector 		 = 0  ;
	ap.param.desc.ds.base 			 = 0  ;
	ap.param.desc.ds.limit 			 = 0xFFFF  ;
	ap.param.desc.ds.access_rights 	 = 0x93  ;	
	ap.param.desc.es.selector 		 = 0  ;
	ap.param.desc.es.base 			 = 0  ;
	ap.param.desc.es.limit 			 = 0xFFFF  ;
	ap.param.desc.es.access_rights 	 = 0x93  ;	
	ap.param.desc.fs.selector 		 = 0  ;
	ap.param.desc.fs.base 			 = 0  ;
	ap.param.desc.fs.limit 			 = 0xFFFF  ;
	ap.param.desc.fs.access_rights 	 = 0x93  ;	
	ap.param.desc.gs.selector 		 = 0  ;
	ap.param.desc.gs.base 			 = 0  ;
	ap.param.desc.gs.limit 			 = 0xFFFF  ;
	ap.param.desc.gs.access_rights 	 = 0x93  ;	
	ap.param.desc.ss.selector 		 = 0  ;
	ap.param.desc.ss.base	 		 = 0  ;
	ap.param.desc.ss.limit 			 = 0xFFFF  ;
	ap.param.desc.ss.access_rights 	 = 0x93  ;	
	//IDTR                             
	ap.param.desc.idtr.base			 = 0  ;
	ap.param.desc.idtr.limit 		 = 0x3ff  ;
	//GDTR                             
	ap.param.desc.gdtr.base			 = 0  ;
	ap.param.desc.gdtr.limit 		 = 0  ;
	//LDTR); unusable                  
	ap.param.desc.ldtr.base			 = 0  ;
	ap.param.desc.ldtr.limit 		 = 0  ;
	ap.param.desc.ldtr.selector		 = 0  ;
	ap.param.desc.ldtr.access_rights = 0x10000 ; 
	//TR); should be usable for VMX to work; not used by guest
	ap.param.desc.tr.base 			 = 0  ;	
	ap.param.desc.tr.limit 			 = 0  ;	
	ap.param.desc.tr.selector 		 = 0  ;	
	ap.param.desc.tr.access_rights 	 = 0x83  ; 	
	xc_api_cpustate_set(context_desc, ap);

}
