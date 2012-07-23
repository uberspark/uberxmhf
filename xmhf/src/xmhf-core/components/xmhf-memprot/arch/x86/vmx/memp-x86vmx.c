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

// EMHF memory protection component
// intel VMX arch. backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

//----------------------------------------------------------------------
// local (static) support function forward declarations
static void _vmx_gathermemorytypes(VCPU *vcpu);
static u32 _vmx_getmemorytypeforphysicalpage(VCPU *vcpu, u64 pagebaseaddr);
static void _vmx_setupEPT(VCPU *vcpu);

//======================================================================
// global interfaces (functions) exported by this component

// initialize memory protection structures for a given core (vcpu)
void emhf_memprot_arch_x86vmx_initialize(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	
	_vmx_gathermemorytypes(vcpu);
	_vmx_setupEPT(vcpu);
	vcpu->vmcs.control_VMX_seccpu_based |= (1 << 1); //enable EPT
	vcpu->vmcs.control_VMX_seccpu_based |= (1 << 5); //enable VPID
	vcpu->vmcs.control_vpid = 1; //VPID=0 is reserved for hypervisor
	vcpu->vmcs.control_EPT_pointer_high = 0;
	vcpu->vmcs.control_EPT_pointer_full = hva2spa((void*)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E; //page walk of 4 and WB memory
	vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
	vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
}


//----------------------------------------------------------------------
// local (static) support functions follow

//---gather memory types for system physical memory------------------------------
static void _vmx_gathermemorytypes(VCPU *vcpu){
 	u32 eax, ebx, ecx, edx;
  u32 index=0;
  
  //0. sanity check
  	//check MTRR support
  	eax=0x00000001;
  	ecx=0x00000000;
  	asm volatile ("cpuid\r\n"
            :"=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
            :"a"(eax), "c" (ecx));
  	if( !(edx & (u32)(1 << 12)) ){
  		printf("\nCPU(0x%02x): CPU does not support MTRRs!", vcpu->id);
  		HALT();
  	}

  	//check MTRR caps
  	rdmsr(IA32_MTRRCAP, &eax, &edx);
  	printf("\nIA32_MTRRCAP: VCNT=%u, FIX=%u, WC=%u, SMRR=%u",
  		(u8)eax, ((eax & (1 << 8)) >> 8),  ((eax & (1 << 10)) >> 10),
  			((eax & (1 << 11)) >> 11));
  	//we need VCNT=8, FIX=1
  	ASSERT( ((eax & (u32)0x000000FF) == 0x8) && ((eax & (1 << 8)) >> 8) );

  //1. clear memorytypes array
  memset((void *)&vcpu->vmx_ept_memorytypes, 0, sizeof(struct _memorytype) * MAX_MEMORYTYPE_ENTRIES);
  
  //2. grab memory types using FIXED MTRRs
    //0x00000000-0x0007FFFF
    rdmsr(IA32_MTRR_FIX64K_00000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00000000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0000FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00010000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0001FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00020000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0002FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00030000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0003FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00040000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0004FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00050000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0005FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00060000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0006FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00070000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0007FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x00080000-0x0009FFFF
  	rdmsr(IA32_MTRR_FIX16K_80000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00080000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x00083FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00084000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x00087FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00088000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0008BFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x0008C000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0008FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00090000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x00093FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00094000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x00097FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x00098000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0009BFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x0009C000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x0009FFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000A0000-0x000BFFFF
	  rdmsr(IA32_MTRR_FIX16K_A0000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000A0000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000A3FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000A4000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000A7FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000A8000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000ABFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000AC000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000AFFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000B0000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000B3FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000B4000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000B7FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000B8000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000BBFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000BC000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000BFFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C0000-0x000C7FFF
    rdmsr(IA32_MTRR_FIX4K_C0000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C0000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C0FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C1000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C1FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C2000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C2FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C3000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C3FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C4000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C4FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C5000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C5FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C6000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C6FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C7000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C7FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C8000-0x000C8FFF
	  rdmsr(IA32_MTRR_FIX4K_C8000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C8000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C8FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000C9000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000C9FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000CA000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000CAFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000CB000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000CBFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000CC000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000CCFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000CD000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000CDFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000CE000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000CEFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000CF000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000CFFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D0000-0x000D7FFF
    rdmsr(IA32_MTRR_FIX4K_D0000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D0000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D0FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D1000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D1FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D2000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D2FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D3000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D3FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D4000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D4FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D5000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D5FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D6000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D6FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D7000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D7FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D8000-0x000DFFFF
  	rdmsr(IA32_MTRR_FIX4K_D8000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D8000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D8FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000D9000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000D9FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000DA000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000DAFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000DB000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000DBFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000DC000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000DCFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000DD000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000DDFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000DE000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000DEFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000DF000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000DFFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E0000-0x000E7FFF
    rdmsr(IA32_MTRR_FIX4K_E0000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E0000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E0FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E1000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E1FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E2000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E2FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E3000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E3FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E4000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E4FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E5000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E5FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E6000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E6FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E7000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E7FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E8000-0x000EFFFF
	  rdmsr(IA32_MTRR_FIX4K_E8000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E8000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E8FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000E9000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000E9FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000EA000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000EAFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000EB000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000EBFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000EC000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000ECFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000ED000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000EDFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000EE000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000EEFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000EF000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000EFFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F0000-0x000F7FFF
  	rdmsr(IA32_MTRR_FIX4K_F0000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F0000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F0FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F1000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F1FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F2000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F2FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F3000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F3FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F4000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F4FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F5000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F5FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F6000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F6FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F7000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F7FFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F8000-0x000FFFFF
  	rdmsr(IA32_MTRR_FIX4K_F8000, &eax, &edx);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F8000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F8FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000F9000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000F9FFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000FA000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000FAFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000FB000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000FBFFF; vcpu->vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000FC000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000FCFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000FD000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000FDFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000FE000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000FEFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    vcpu->vmx_ept_memorytypes[index].startaddr = 0x000FF000; vcpu->vmx_ept_memorytypes[index].endaddr = 0x000FFFFF; vcpu->vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
	       
  //3. grab memory types using variable length MTRRs  
  {
		u64 paddrmask = 0x0000000FFFFFFFFFULL; //36-bits physical address, TODO: need to make this dynamic
		u64 vMTRR_base, vMTRR_mask;
		u32 msrval=IA32_MTRR_PHYSBASE0;
		u32 i;
		
		for(i=0; i < 8; i++){
			rdmsr(msrval, &eax, &edx);
			vMTRR_base = ((u64)edx << 32) | (u64)eax;
			msrval++;
			rdmsr(msrval, &eax, &edx);
			vMTRR_mask = ((u64)edx << 32) | (u64)eax;
			msrval++;
			if( (vMTRR_mask & ((u64)1 << 11)) ){
        vcpu->vmx_ept_memorytypes[index].startaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL);
        vcpu->vmx_ept_memorytypes[index].endaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL) + 
					(u64) (~(vMTRR_mask & (u64)0xFFFFFFFFFFFFF000ULL) &
						paddrmask);
        vcpu->vmx_ept_memorytypes[index++].type = ((u32)vMTRR_base & (u32)0x000000FF);       
      }else{
        vcpu->vmx_ept_memorytypes[index++].invalid = 1;
      }
		}
	}

  ASSERT( index == MAX_MEMORYTYPE_ENTRIES);


  //[debug: dump the contents of vcpu->vmx_ept_memorytypes]
  //{
  //  int i;
  //  for(i=0; i < MAX_MEMORYTYPE_ENTRIES; i++){
  //    printf("\nrange  0x%016llx-0x%016llx (type=%u)", 
  //      vcpu->vmx_ept_memorytypes[i].startaddr, vcpu->vmx_ept_memorytypes[i].endaddr, vcpu->vmx_ept_memorytypes[i].type);
  //  }
  //}
  
  //[test]
  //printf("\ntype for page base 0x00000000 = %u", vmx_getmemorytypeforphysicalpage((u64)0) );
  //printf("\ntype for page base 0x000F0000 = %u", vmx_getmemorytypeforphysicalpage((u64)0x000F0000) );
  //printf("\ntype for page base 0xC0000000 = %u", vmx_getmemorytypeforphysicalpage((u64)0xC0000000) );
  
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
static u32 _vmx_getmemorytypeforphysicalpage(VCPU *vcpu, u64 pagebaseaddr){
 int i;
 u32 prev_type= MTRR_TYPE_RESV; 

  //check if page base address under 1M, if so used FIXED MTRRs
  if(pagebaseaddr < (1024*1024)){
    for(i=0; i < MAX_FIXED_MEMORYTYPE_ENTRIES; i++){
      if( pagebaseaddr >= vcpu->vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= vcpu->vmx_ept_memorytypes[i].endaddr )
        return vcpu->vmx_ept_memorytypes[i].type;    
    }
    
    printf("\n%s: endaddr < 1M and unmatched fixed MTRR. Halt!", __FUNCTION__);
    HALT();
  }
 
  //page base address is above 1M, use VARIABLE MTRRs
  for(i= MAX_FIXED_MEMORYTYPE_ENTRIES; i < MAX_MEMORYTYPE_ENTRIES; i++){
    if( pagebaseaddr >= vcpu->vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= vcpu->vmx_ept_memorytypes[i].endaddr && 
          (!vcpu->vmx_ept_memorytypes[i].invalid) ){
       if(vcpu->vmx_ept_memorytypes[i].type == MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_UC;
       }else if(vcpu->vmx_ept_memorytypes[i].type == MTRR_TYPE_WT && prev_type != MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_WT;
       }else{
        if(prev_type != MTRR_TYPE_UC && prev_type != MTRR_TYPE_WT){
          if(prev_type == MTRR_TYPE_RESV){
            prev_type = vcpu->vmx_ept_memorytypes[i].type;
          }else{
            printf("\nprev_type=%u, vcpu->vmx_ept_memorytypes=%u", prev_type, vcpu->vmx_ept_memorytypes[i].type);
            ASSERT ( prev_type == vcpu->vmx_ept_memorytypes[i].type);
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
static void _vmx_setupEPT(VCPU *vcpu){
	//step-1: tie in EPT PML4 structures
	//note: the default memory type (usually WB) should be determined using 
	//IA32_MTRR_DEF_TYPE_MSR. If MTRR's are not enabled (really?)
	//then all default memory is type UC (uncacheable)
	u64 *pml4_table, *pdp_table, *pd_table, *p_table;
	u32 i, j, k, paddr=0;

	pml4_table = (u64 *)vcpu->vmx_vaddr_ept_pml4_table;
	pml4_table[0] = (u64) (hva2spa((void*)vcpu->vmx_vaddr_ept_pdp_table) | 0x7); 

	pdp_table = (u64 *)vcpu->vmx_vaddr_ept_pdp_table;
		
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		pdp_table[i] = (u64) ( hva2spa((void*)vcpu->vmx_vaddr_ept_pd_tables + (PAGE_SIZE_4K * i)) | 0x7 );
		pd_table = (u64 *)  ((u32)vcpu->vmx_vaddr_ept_pd_tables + (PAGE_SIZE_4K * i)) ;
		
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			pd_table[j] = (u64) ( hva2spa((void*)vcpu->vmx_vaddr_ept_p_tables + (PAGE_SIZE_4K * ((i*PAE_PTRS_PER_PDT)+j))) | 0x7 );
			p_table = (u64 *)  ((u32)vcpu->vmx_vaddr_ept_p_tables + (PAGE_SIZE_4K * ((i*PAE_PTRS_PER_PDT)+j))) ;
			
			for(k=0; k < PAE_PTRS_PER_PT; k++){
				u32 memorytype = _vmx_getmemorytypeforphysicalpage(vcpu, (u64)paddr);
				//the EMHF memory region includes the secure loader +
				//the runtime (core + app). this runs from 
				//(rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M) with a size
				//of (rpb->XtVmmRuntimeSize+PAGE_SIZE_2M)
				//make EMHF physical pages inaccessible
				if( (paddr >= (rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M)) &&
					(paddr < (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize)) ){
					p_table[k] = (u64) (paddr)  | ((u64)memorytype << 3) | (u64)0x0 ;	//not-present
				}else{
					if(memorytype == 0)
						p_table[k] = (u64) (paddr)  | ((u64)memorytype << 3) |  (u64)0x7 ;	//present, UC
					else
						p_table[k] = (u64) (paddr)  | ((u64)6 << 3) | (u64)0x7 ;	//present, WB, track host MTRR
				}
				
				paddr += PAGE_SIZE_4K;
			}
		}
	}

}


//flush hardware page table mappings (TLB) 
void emhf_memprot_arch_x86vmx_flushmappings(VCPU *vcpu){
  __vmx_invept(VMX_INVEPT_SINGLECONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full);
  //__vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}


//set protection for a given physical memory address
void emhf_memprot_arch_x86vmx_setprot(VCPU *vcpu, u64 gpa, u32 prottype){
  u32 pfn;
  u64 *pt;
  u32 flags =0;
  
  pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  
  //default is not-present, read-only, no-execute	
  pt[pfn] &= ~(u64)7; //clear all previous flags

  //map high level protection type to EPT protection bits
  if(prottype & MEMP_PROT_PRESENT){
	flags=1;	//present is defined by the read bit in EPT
	
	if(prottype & MEMP_PROT_READWRITE)
		flags |= 0x2;
		
	if(prottype & MEMP_PROT_EXECUTE)
		flags |= 0x4;
  }
  	
  //set new flags
  pt[pfn] |= flags; 
}


//get protection for a given physical memory address
u32 emhf_memprot_arch_x86vmx_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  //u64 *pt = (u64 *)(u32)emhf_memprot_arch_x86vmx_get_EPTP(vcpu); //TODO: push into vmx sub arch. backend
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  u64 entry = pt[pfn];
  u32 prottype;
  
  if(! (entry & 0x1) ){
	prottype = MEMP_PROT_NOTPRESENT;
	return prottype;
  }
 
  prottype = MEMP_PROT_PRESENT;
  
  if( entry & 0x2 )
	prottype |= MEMP_PROT_READWRITE;
  else
	prottype |= MEMP_PROT_READONLY;

  if( entry & 0x4 )
	prottype |= MEMP_PROT_EXECUTE;
  else
	prottype |= MEMP_PROT_NOEXECUTE;

  return prottype;
}

u64 emhf_memprot_arch_x86vmx_get_EPTP(VCPU *vcpu)
{
  ASSERT(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
  return
    ((u64)(vcpu->vmcs.control_EPT_pointer_high) << 32)
    | (u64)(vcpu->vmcs.control_EPT_pointer_full);
}
void emhf_memprot_arch_x86vmx_set_EPTP(VCPU *vcpu, u64 eptp)
{
  ASSERT(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
  vcpu->vmcs.control_EPT_pointer_full = (u32)eptp;
  vcpu->vmcs.control_EPT_pointer_high = (u32)(eptp >> 32);
}
