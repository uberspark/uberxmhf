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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

//------------------------------------------------------------------------------
// islayer_ug.c
// isolation layer code specific to  
// VMX impl. with unrestricted guest caps.
// author: amit vasudevan (amitvasudevan@acm.org) 

#include <target.h>
#include <globals.h>

//---globals referenced by this module------------------------------------------
extern u32 x_gdt_start[], x_idt_start[]; //runtimesup.S
extern void __vmx_callback(void);	//islayersup_vmx.S


//critical MSRs that need to be saved/restored across guest VM switches
static const u32 vmx_msr_area_msrs[] = {
	MSR_EFER, 
	MSR_K6_STAR,
};
//count of critical MSRs that need to be saved/restored across VM switches
static const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));


//---VMX decode assist----------------------------------------------------------
//map a CPU register index into appropriate VCPU *vcpu or struct regs *r field 
//and return the address of the field
static u32 * _vmx_decode_reg(u32 gpr, VCPU *vcpu, struct regs *r){
  ASSERT ( ((int)gpr >=0) && ((int)gpr <= 7) );
  
  switch(gpr){
    case 0: return ( (u32 *)&r->eax );
    case 1: return ( (u32 *)&r->ecx );
    case 2: return ( (u32 *)&r->edx );
    case 3: return ( (u32 *)&r->ebx );
    case 4: return ( (u32 *)&vcpu->vmcs.guest_RSP);
    case 5: return ( (u32 *)&r->ebp );
    case 6: return ( (u32 *)&r->esi );
    case 7: return ( (u32 *)&r->edi );
  }

  return NULL; /* unreachable */
}


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
/*
11.11.4.1 MTRR Precedences
  0. if MTRRs are not enabled --> MTRR_TYPE_UC
  if enabled then
     if physaddr < 1MB use fixed MTRR ranges return type
     else if within a valid variable range MTRR then
        if a single match, return type
        if two or more and one is UC, return UC
        if two or more and WB and WT, return WT
        else invalid combination
     else
        return default memory type
*/
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
	pml4_table[0] = (u64) (__hva2spa__((u32)vcpu->vmx_vaddr_ept_pdp_table) | 0x7); 

	pdp_table = (u64 *)vcpu->vmx_vaddr_ept_pdp_table;
		
	for(i=0; i < 4; i++){
		pdp_table[i] = (u64) ( __hva2spa__((u32)vcpu->vmx_vaddr_ept_pd_tables + (4096 * i)) | 0x7 );
		pd_table = (u64 *)  ((u32)vcpu->vmx_vaddr_ept_pd_tables + (4096 * i)) ;
		
		for(j=0; j < 512; j++){
			pd_table[j] = (u64) ( __hva2spa__((u32)vcpu->vmx_vaddr_ept_p_tables + (4096 * ((i*512)+j))) | 0x7 );
			p_table = (u64 *)  ((u32)vcpu->vmx_vaddr_ept_p_tables + (4096 * ((i*512)+j))) ;
			
			for(k=0; k < 512; k++){
				u32 memorytype = _vmx_getmemorytypeforphysicalpage(vcpu, (u64)paddr);
				p_table[k] = (u64) (paddr)  | ((u64)memorytype << 3) | (u64)0x7 ;
				paddr += 4096;
			}
		}
	}

	/* TODO: mark all the physical pages of EMHF hyervisor not present */
}



//--initunrestrictedguestVMCS: initializes VMCS for unrestricted guest ---------
void vmx_initunrestrictedguestVMCS(VCPU *vcpu){
		u32 lodword, hidword;

			//clear VMCS
			memset((void *)&vcpu->vmcs, 0, sizeof(struct _vmx_vmcsfields));
			
			//setup host state
			vcpu->vmcs.host_CR0 = read_cr0();
			vcpu->vmcs.host_CR4 = read_cr4();
			vcpu->vmcs.host_CR3 = read_cr3();
			vcpu->vmcs.host_CS_selector = read_segreg_cs();
			vcpu->vmcs.host_DS_selector = read_segreg_ds();
			vcpu->vmcs.host_ES_selector = read_segreg_es();
			vcpu->vmcs.host_FS_selector = read_segreg_fs();
			vcpu->vmcs.host_GS_selector = read_segreg_gs();
			vcpu->vmcs.host_SS_selector = read_segreg_ss();
			vcpu->vmcs.host_TR_selector = read_tr_sel();
			vcpu->vmcs.host_GDTR_base = (u64)(u32)x_gdt_start;
			vcpu->vmcs.host_IDTR_base = (u64)(u32)x_idt_start;
			vcpu->vmcs.host_TR_base = (u64)(u32)g_runtime_TSS;
			vcpu->vmcs.host_RIP = (u64)(u32)__vmx_callback;
			vcpu->vmcs.host_RSP = (u64)vcpu->esp;
			rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_CS = lodword;
      rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_ESP = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_EIP = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
      vcpu->vmcs.host_FS_base = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
      vcpu->vmcs.host_GS_base = (u64) (((u64)hidword << 32) | (u64)lodword);

      //setup default VMX controls
 			vcpu->vmcs.control_VMX_pin_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR];
      vcpu->vmcs.control_VMX_cpu_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR];
			vcpu->vmcs.control_VM_exit_controls = vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR];
 			vcpu->vmcs.control_VM_entry_controls = vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR];
      
 			//IO bitmap support
			vcpu->vmcs.control_IO_BitmapA_address_full = (u32)__hva2spa__((u32)vcpu->vmx_vaddr_iobitmap);
			vcpu->vmcs.control_IO_BitmapA_address_high = 0;
			vcpu->vmcs.control_IO_BitmapB_address_full = (u32)__hva2spa__( ((u32)vcpu->vmx_vaddr_iobitmap + PAGE_SIZE_4K) );
			vcpu->vmcs.control_IO_BitmapB_address_high = 0;
			vcpu->vmcs.control_VMX_cpu_based |= (1 << 25); //enable use IO Bitmaps

 			//MSR bitmap support
			//memset( (void *)vcpu->vmx_vaddr_msrbitmaps, 0xFFFFFFFFUL, PAGE_SIZE_4K); //trap all MSR accesses
			//vcpu->vmcs.control_MSR_Bitmaps_address_full = (u32)__hva2spa__((u32)vcpu->vmx_vaddr_msrbitmaps);	 							
			//vcpu->vmcs.control_MSR_Bitmaps_address_high = 0;
			//vcpu->vmcs.control_VMX_cpu_based |= (1 << 28); //enable use MSR Bitmaps 


#if 1
			//Critical MSR load/store
			{
					u32 i;
  				msr_entry_t *hmsr = (msr_entry_t *)vcpu->vmx_vaddr_msr_area_host;
					msr_entry_t *gmsr = (msr_entry_t *)vcpu->vmx_vaddr_msr_area_guest;

					//store initial values of the MSRs
					for(i=0; i < vmx_msr_area_msrs_count; i++){
						u32 msr, eax, edx;
	          msr = vmx_msr_area_msrs[i];						
						rdmsr(msr, &eax, &edx);
						hmsr[i].index = gmsr[i].index = msr;
						hmsr[i].data = gmsr[i].data = ((u64)edx << 32) | (u64)eax;
					}
					
					//host MSR load on exit, we store it ourselves before entry
					vcpu->vmcs.control_VM_exit_MSR_load_address_full=(u32)__hva2spa__((u32)vcpu->vmx_vaddr_msr_area_host);
					vcpu->vmcs.control_VM_exit_MSR_load_address_high=0;
					vcpu->vmcs.control_VM_exit_MSR_load_count= vmx_msr_area_msrs_count;
					
					//guest MSR load on entry, store on exit
					vcpu->vmcs.control_VM_entry_MSR_load_address_full=(u32)__hva2spa__((u32)vcpu->vmx_vaddr_msr_area_guest);
					vcpu->vmcs.control_VM_entry_MSR_load_address_high=0;
					vcpu->vmcs.control_VM_entry_MSR_load_count=vmx_msr_area_msrs_count;
				  vcpu->vmcs.control_VM_exit_MSR_store_address_full=(u32)__hva2spa__((u32)vcpu->vmx_vaddr_msr_area_guest);
					vcpu->vmcs.control_VM_exit_MSR_store_address_high=0;
					vcpu->vmcs.control_VM_exit_MSR_store_count=vmx_msr_area_msrs_count;
			}
#endif


			vcpu->vmcs.control_pagefault_errorcode_mask  = 0x00000000;	//dont be concerned with 
			vcpu->vmcs.control_pagefault_errorcode_match = 0x00000000; //guest page-faults
			vcpu->vmcs.control_exception_bitmap = 0;
			vcpu->vmcs.control_CR3_target_count = 0;
      
      //setup guest state
      	//CR0, real-mode, PE and PG bits cleared
     		vcpu->vmcs.guest_CR0 = vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];
     		vcpu->vmcs.guest_CR0 &= ~(CR0_PE);
     		vcpu->vmcs.guest_CR0 &= ~(CR0_PG);
     		//CR4, required bits set (usually VMX enabled bit)
   			vcpu->vmcs.guest_CR4 = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];
				//CR3 set to 0, does not matter
				vcpu->vmcs.guest_CR3 = 0;
				//IDTR
				vcpu->vmcs.guest_IDTR_base = 0;
				vcpu->vmcs.guest_IDTR_limit = 0x3ff;	//16-bit IVT
				//GDTR
				vcpu->vmcs.guest_GDTR_base = 0;
				vcpu->vmcs.guest_GDTR_limit = 0;	//no GDT
				//LDTR, unusable
				vcpu->vmcs.guest_LDTR_base = 0;
				vcpu->vmcs.guest_LDTR_limit = 0;
				vcpu->vmcs.guest_LDTR_selector = 0;
				vcpu->vmcs.guest_LDTR_access_rights = 0x10000;
				//TR, should be usable for VMX to work, but not used by guest
				vcpu->vmcs.guest_TR_base = 0;
				vcpu->vmcs.guest_TR_limit = 0;
				vcpu->vmcs.guest_TR_selector = 0;
				vcpu->vmcs.guest_TR_access_rights = 0x83; //present, 16-bit busy TSS
				//RSP
				vcpu->vmcs.guest_RSP = 0x0;
				//RIP
			  if(vmx_isbsp()){
			    printf("\nBSP(0x%02x): copying boot-module to boot guest", vcpu->id);
  				memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)rpb->XtGuestOSBootModuleBase, rpb->XtGuestOSBootModuleSize);
					vcpu->vmcs.guest_CS_selector = 0;
					vcpu->vmcs.guest_CS_base = 0;
    			vcpu->vmcs.guest_RIP = 0x7c00ULL;
  			}else{
      		vcpu->vmcs.guest_CS_selector = (vcpu->sipivector * PAGE_SIZE_4K) >> 4;
      		vcpu->vmcs.guest_CS_base = (vcpu->sipivector * PAGE_SIZE_4K);
      		vcpu->vmcs.guest_RIP = 0x0ULL;
				}
			
			
				//vcpu->vmcs.guest_RIP = 0x7c00;
				//vcpu->vmcs.guest_CS_selector = 0;
				//vcpu->vmcs.guest_CS_base = 0;
				
				vcpu->vmcs.guest_CS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_CS_access_rights = 0x93; //present, system, read-write accessed
				
				//RFLAGS
				vcpu->vmcs.guest_RFLAGS = 0; 
				vcpu->vmcs.guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
				vcpu->vmcs.guest_RFLAGS |= (1<<1);				// reserved 1-bits
				vcpu->vmcs.guest_RFLAGS |= (1<<9);				// IF = enable 
				vcpu->vmcs.guest_RFLAGS &= ~(1<<14);			// Nested Task = disable
				//CS, DS, ES, FS, GS and SS segments
				vcpu->vmcs.guest_DS_selector = 0;
				vcpu->vmcs.guest_DS_base = 0;
				vcpu->vmcs.guest_DS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_DS_access_rights = 0x93; //present, system, read-write accessed
				vcpu->vmcs.guest_ES_selector = 0;
				vcpu->vmcs.guest_ES_base = 0;
				vcpu->vmcs.guest_ES_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_ES_access_rights = 0x93; //present, system, read-write accessed
				vcpu->vmcs.guest_FS_selector = 0;
				vcpu->vmcs.guest_FS_base = 0;
				vcpu->vmcs.guest_FS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_FS_access_rights = 0x93; //present, system, read-write accessed
				vcpu->vmcs.guest_GS_selector = 0;
				vcpu->vmcs.guest_GS_base = 0;
				vcpu->vmcs.guest_GS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_GS_access_rights = 0x93; //present, system, read-write accessed
				vcpu->vmcs.guest_SS_selector = 0x0;
				vcpu->vmcs.guest_SS_base = 0x0;
				vcpu->vmcs.guest_SS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_SS_access_rights = 0x93; //present, system, read-write accessed

			//activate secondary processor controls
      vcpu->vmcs.control_VMX_seccpu_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR];
			vcpu->vmcs.control_VMX_cpu_based |= (1 << 31); //activate secondary processor controls

#if defined (__NESTED_PAGING__)
      //setup EPT
      _vmx_gathermemorytypes(vcpu);
      _vmx_setupEPT(vcpu);
			vcpu->vmcs.control_VMX_seccpu_based |= (1 << 1); //enable EPT
			vcpu->vmcs.control_VMX_seccpu_based |= (1 << 5); //enable VPID
 			vcpu->vmcs.control_vpid = 1; //VPID=0 is reserved for hypervisor
 			vcpu->vmcs.control_EPT_pointer_high = 0;
 			vcpu->vmcs.control_EPT_pointer_full = __hva2spa__((u32)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E; //page walk of 4 and WB memory
			vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
			vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
#endif

			//setup unrestricted guest
			vcpu->vmcs.control_VMX_seccpu_based |= (1 << 7); //enable unrestricted guest
			
			//setup VMCS link pointer
		  vcpu->vmcs.guest_VMCS_link_pointer_full = (u32)0xFFFFFFFFUL;
			vcpu->vmcs.guest_VMCS_link_pointer_high = (u32)0xFFFFFFFFUL;
	
			//setup NMI intercept for core-quiescing
			vcpu->vmcs.control_VMX_pin_based |= (1 << 3);	//intercept NMIs
	
			
			//trap access to CR4 fixed bits (this includes the VMXE bit)
			vcpu->vmcs.control_CR4_mask = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];  
			vcpu->vmcs.control_CR4_shadow = CR4_VMXE; //let guest know we have VMX enabled

	
			//flush guest TLB to start with
			__vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}


//---CR4 access handler---------------------------------------------------------
void vmx_handle_intercept_cr4access_ug(VCPU *vcpu, struct regs *r, u32 gpr, u32 tofrom){
	ASSERT(tofrom == VMX_CRX_ACCESS_TO);

  printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x MOV CR4, xx", vcpu->id,
    (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
  
	printf("\nMOV TO CR4 (flush TLB?), current=0x%08x, proposed=0x%08x",
			(u32)vcpu->vmcs.guest_CR4, *((u32 *)_vmx_decode_reg(gpr, vcpu, r)) );

  #if defined (__NESTED_PAGING__)
  //we need to flush EPT mappings as we emulated CR4 load above
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
  #endif

}
