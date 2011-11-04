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
// hardware_paging.c
//
// intel vt-x hypervisor memory isolation using extended
// page tables
//
// author: amit vasudevan (amitvasudevan@acm.org)

/* our system memory type map
00000000-0009ffff = 6
000a0000-000dffff = 0
000e0000-000e3fff = 5
000e4000-000e7fff = 4
000e8000-000ebfff = 5
000ec000-000effff = 4
000f0000-000fffff = 5
00100000-bf7fffff = 6
bf800000-ffffffff = 0
*/

/*
range  0x0000000000000000-0x000000000000ffff (type=6)
range  0x0000000000010000-0x000000000001ffff (type=6)
range  0x0000000000020000-0x000000000002ffff (type=6)
range  0x0000000000030000-0x000000000003ffff (type=6)
range  0x0000000000040000-0x000000000004ffff (type=6)
range  0x0000000000050000-0x000000000005ffff (type=6)
range  0x0000000000060000-0x000000000006ffff (type=6)
range  0x0000000000070000-0x000000000007ffff (type=6)
range  0x0000000000080000-0x0000000000083fff (type=6)
range  0x0000000000084000-0x0000000000087fff (type=6)
range  0x0000000000088000-0x000000000008bfff (type=6)
range  0x000000000008c000-0x000000000008ffff (type=6)
range  0x0000000000090000-0x0000000000093fff (type=6)
range  0x0000000000094000-0x0000000000097fff (type=6)
range  0x0000000000098000-0x000000000009bfff (type=6)
range  0x000000000009c000-0x000000000009ffff (type=6)
range  0x00000000000a0000-0x00000000000a3fff (type=0)
range  0x00000000000a4000-0x00000000000a7fff (type=0)
range  0x00000000000a8000-0x00000000000abfff (type=0)
range  0x00000000000ac000-0x00000000000affff (type=0)
range  0x00000000000b0000-0x00000000000b3fff (type=0)
range  0x00000000000b4000-0x00000000000b7fff (type=0)
range  0x00000000000b8000-0x00000000000bbfff (type=0)
range  0x00000000000bc000-0x00000000000bffff (type=0)
range  0x00000000000c0000-0x00000000000c0fff (type=0)
range  0x00000000000c1000-0x00000000000c1fff (type=0)
range  0x00000000000c2000-0x00000000000c2fff (type=0)
range  0x00000000000c3000-0x00000000000c3fff (type=0)
range  0x00000000000c4000-0x00000000000c4fff (type=0)
range  0x00000000000c5000-0x00000000000c5fff (type=0)
range  0x00000000000c6000-0x00000000000c6fff (type=0)
range  0x00000000000c7000-0x00000000000c7fff (type=0)
range  0x00000000000c8000-0x00000000000c8fff (type=0)
range  0x00000000000c9000-0x00000000000c9fff (type=0)
range  0x00000000000ca000-0x00000000000cafff (type=0)
range  0x00000000000cb000-0x00000000000cbfff (type=0)
range  0x00000000000cc000-0x00000000000ccfff (type=0)
range  0x00000000000cd000-0x00000000000cdfff (type=0)
range  0x00000000000ce000-0x00000000000cefff (type=0)
range  0x00000000000cf000-0x00000000000cffff (type=0)
range  0x00000000000d0000-0x00000000000d0fff (type=0)
range  0x00000000000d1000-0x00000000000d1fff (type=0)
range  0x00000000000d2000-0x00000000000d2fff (type=0)
range  0x00000000000d3000-0x00000000000d3fff (type=0)
range  0x00000000000d4000-0x00000000000d4fff (type=0)
range  0x00000000000d5000-0x00000000000d5fff (type=0)
range  0x00000000000d6000-0x00000000000d6fff (type=0)
range  0x00000000000d7000-0x00000000000d7fff (type=0)
range  0x00000000000d8000-0x00000000000d8fff (type=0)
range  0x00000000000d9000-0x00000000000d9fff (type=0)
range  0x00000000000da000-0x00000000000dafff (type=0)
range  0x00000000000db000-0x00000000000dbfff (type=0)
range  0x00000000000dc000-0x00000000000dcfff (type=0)
range  0x00000000000dd000-0x00000000000ddfff (type=0)
range  0x00000000000de000-0x00000000000defff (type=0)
range  0x00000000000df000-0x00000000000dffff (type=0)
range  0x00000000000e0000-0x00000000000e0fff (type=5)
range  0x00000000000e1000-0x00000000000e1fff (type=5)
range  0x00000000000e2000-0x00000000000e2fff (type=5)
range  0x00000000000e3000-0x00000000000e3fff (type=5)
range  0x00000000000e4000-0x00000000000e4fff (type=4)
range  0x00000000000e5000-0x00000000000e5fff (type=4)
range  0x00000000000e6000-0x00000000000e6fff (type=4)
range  0x00000000000e7000-0x00000000000e7fff (type=4)
range  0x00000000000e8000-0x00000000000e8fff (type=5)
range  0x00000000000e9000-0x00000000000e9fff (type=5)
range  0x00000000000ea000-0x00000000000eafff (type=5)
range  0x00000000000eb000-0x00000000000ebfff (type=5)
range  0x00000000000ec000-0x00000000000ecfff (type=4)
range  0x00000000000ed000-0x00000000000edfff (type=4)
range  0x00000000000ee000-0x00000000000eefff (type=4)
range  0x00000000000ef000-0x00000000000effff (type=4)
range  0x00000000000f0000-0x00000000000f0fff (type=5)
range  0x00000000000f1000-0x00000000000f1fff (type=5)
range  0x00000000000f2000-0x00000000000f2fff (type=5)
range  0x00000000000f3000-0x00000000000f3fff (type=5)
range  0x00000000000f4000-0x00000000000f4fff (type=5)
range  0x00000000000f5000-0x00000000000f5fff (type=5)
range  0x00000000000f6000-0x00000000000f6fff (type=5)
range  0x00000000000f7000-0x00000000000f7fff (type=5)
range  0x00000000000f8000-0x00000000000f8fff (type=5)
range  0x00000000000f9000-0x00000000000f9fff (type=5)
range  0x00000000000fa000-0x00000000000fafff (type=5)
range  0x00000000000fb000-0x00000000000fbfff (type=5)
range  0x00000000000fc000-0x00000000000fcfff (type=5)
range  0x00000000000fd000-0x00000000000fdfff (type=5)
range  0x00000000000fe000-0x00000000000fefff (type=5)
range  0x00000000000ff000-0x00000000000fffff (type=5)
range  0x0000000000000000-0x00000000ffffffff (type=6)
range  0x0000000100000000-0x000000013fffffff (type=6)
range  0x00000000c0000000-0x00000000ffffffff (type=0)
range  0x00000000bf800000-0x00000000bfffffff (type=0)
range  0x0000000000000000-0x0000000000000000 (type=0)
range  0x0000000000000000-0x0000000000000000 (type=0)
range  0x0000000000000000-0x0000000000000000 (type=0)
range  0x0000000000000000-0x0000000000000000 (type=0)


*/

#include <target.h>


struct _memorytype {
  u64 startaddr;
  u64 endaddr;
  u32 type;
  u32 invalid;
  u32 reserved[6];
} __attribute__((packed));

#define MAX_MEMORYTYPE_ENTRIES    96    //8*11 fixed MTRRs and 8 variable MTRRs
#define MAX_FIXED_MEMORYTYPE_ENTRIES  88
#define MAX_VARIABLE_MEMORYTYPE_ENTRIES 8

struct _memorytype  memorytypes[MAX_MEMORYTYPE_ENTRIES];

//---gather memory types for system physical memory------------------------------
void vmx_gathermemorytypes(VCPU *vcpu){
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
  memset((void *)&memorytypes, 0, sizeof(memorytypes));
  
  //2. grab memory types using FIXED MTRRs
    //0x00000000-0x0007FFFF
    rdmsr(IA32_MTRR_FIX64K_00000, &eax, &edx);
    memorytypes[index].startaddr = 0x00000000; memorytypes[index].endaddr = 0x0000FFFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x00010000; memorytypes[index].endaddr = 0x0001FFFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x00020000; memorytypes[index].endaddr = 0x0002FFFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x00030000; memorytypes[index].endaddr = 0x0003FFFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x00040000; memorytypes[index].endaddr = 0x0004FFFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x00050000; memorytypes[index].endaddr = 0x0005FFFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x00060000; memorytypes[index].endaddr = 0x0006FFFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x00070000; memorytypes[index].endaddr = 0x0007FFFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x00080000-0x0009FFFF
  	rdmsr(IA32_MTRR_FIX16K_80000, &eax, &edx);
    memorytypes[index].startaddr = 0x00080000; memorytypes[index].endaddr = 0x00083FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x00084000; memorytypes[index].endaddr = 0x00087FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x00088000; memorytypes[index].endaddr = 0x0008BFFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x0008C000; memorytypes[index].endaddr = 0x0008FFFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x00090000; memorytypes[index].endaddr = 0x00093FFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x00094000; memorytypes[index].endaddr = 0x00097FFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x00098000; memorytypes[index].endaddr = 0x0009BFFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x0009C000; memorytypes[index].endaddr = 0x0009FFFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000A0000-0x000BFFFF
	  rdmsr(IA32_MTRR_FIX16K_A0000, &eax, &edx);
    memorytypes[index].startaddr = 0x000A0000; memorytypes[index].endaddr = 0x000A3FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000A4000; memorytypes[index].endaddr = 0x000A7FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000A8000; memorytypes[index].endaddr = 0x000ABFFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000AC000; memorytypes[index].endaddr = 0x000AFFFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000B0000; memorytypes[index].endaddr = 0x000B3FFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000B4000; memorytypes[index].endaddr = 0x000B7FFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000B8000; memorytypes[index].endaddr = 0x000BBFFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000BC000; memorytypes[index].endaddr = 0x000BFFFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C0000-0x000C7FFF
    rdmsr(IA32_MTRR_FIX4K_C0000, &eax, &edx);
    memorytypes[index].startaddr = 0x000C0000; memorytypes[index].endaddr = 0x000C0FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000C1000; memorytypes[index].endaddr = 0x000C1FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000C2000; memorytypes[index].endaddr = 0x000C2FFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000C3000; memorytypes[index].endaddr = 0x000C3FFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000C4000; memorytypes[index].endaddr = 0x000C4FFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000C5000; memorytypes[index].endaddr = 0x000C5FFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000C6000; memorytypes[index].endaddr = 0x000C6FFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000C7000; memorytypes[index].endaddr = 0x000C7FFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C8000-0x000C8FFF
	  rdmsr(IA32_MTRR_FIX4K_C8000, &eax, &edx);
    memorytypes[index].startaddr = 0x000C8000; memorytypes[index].endaddr = 0x000C8FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000C9000; memorytypes[index].endaddr = 0x000C9FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000CA000; memorytypes[index].endaddr = 0x000CAFFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000CB000; memorytypes[index].endaddr = 0x000CBFFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000CC000; memorytypes[index].endaddr = 0x000CCFFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000CD000; memorytypes[index].endaddr = 0x000CDFFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000CE000; memorytypes[index].endaddr = 0x000CEFFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000CF000; memorytypes[index].endaddr = 0x000CFFFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D0000-0x000D7FFF
    rdmsr(IA32_MTRR_FIX4K_D0000, &eax, &edx);
    memorytypes[index].startaddr = 0x000D0000; memorytypes[index].endaddr = 0x000D0FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000D1000; memorytypes[index].endaddr = 0x000D1FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000D2000; memorytypes[index].endaddr = 0x000D2FFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000D3000; memorytypes[index].endaddr = 0x000D3FFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000D4000; memorytypes[index].endaddr = 0x000D4FFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000D5000; memorytypes[index].endaddr = 0x000D5FFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000D6000; memorytypes[index].endaddr = 0x000D6FFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000D7000; memorytypes[index].endaddr = 0x000D7FFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D8000-0x000DFFFF
  	rdmsr(IA32_MTRR_FIX4K_D8000, &eax, &edx);
    memorytypes[index].startaddr = 0x000D8000; memorytypes[index].endaddr = 0x000D8FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000D9000; memorytypes[index].endaddr = 0x000D9FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000DA000; memorytypes[index].endaddr = 0x000DAFFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000DB000; memorytypes[index].endaddr = 0x000DBFFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000DC000; memorytypes[index].endaddr = 0x000DCFFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000DD000; memorytypes[index].endaddr = 0x000DDFFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000DE000; memorytypes[index].endaddr = 0x000DEFFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000DF000; memorytypes[index].endaddr = 0x000DFFFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E0000-0x000E7FFF
    rdmsr(IA32_MTRR_FIX4K_E0000, &eax, &edx);
    memorytypes[index].startaddr = 0x000E0000; memorytypes[index].endaddr = 0x000E0FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000E1000; memorytypes[index].endaddr = 0x000E1FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000E2000; memorytypes[index].endaddr = 0x000E2FFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000E3000; memorytypes[index].endaddr = 0x000E3FFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000E4000; memorytypes[index].endaddr = 0x000E4FFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000E5000; memorytypes[index].endaddr = 0x000E5FFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000E6000; memorytypes[index].endaddr = 0x000E6FFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000E7000; memorytypes[index].endaddr = 0x000E7FFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E8000-0x000EFFFF
	  rdmsr(IA32_MTRR_FIX4K_E8000, &eax, &edx);
    memorytypes[index].startaddr = 0x000E8000; memorytypes[index].endaddr = 0x000E8FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000E9000; memorytypes[index].endaddr = 0x000E9FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000EA000; memorytypes[index].endaddr = 0x000EAFFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000EB000; memorytypes[index].endaddr = 0x000EBFFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000EC000; memorytypes[index].endaddr = 0x000ECFFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000ED000; memorytypes[index].endaddr = 0x000EDFFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000EE000; memorytypes[index].endaddr = 0x000EEFFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000EF000; memorytypes[index].endaddr = 0x000EFFFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F0000-0x000F7FFF
  	rdmsr(IA32_MTRR_FIX4K_F0000, &eax, &edx);
    memorytypes[index].startaddr = 0x000F0000; memorytypes[index].endaddr = 0x000F0FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000F1000; memorytypes[index].endaddr = 0x000F1FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000F2000; memorytypes[index].endaddr = 0x000F2FFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000F3000; memorytypes[index].endaddr = 0x000F3FFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000F4000; memorytypes[index].endaddr = 0x000F4FFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000F5000; memorytypes[index].endaddr = 0x000F5FFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000F6000; memorytypes[index].endaddr = 0x000F6FFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000F7000; memorytypes[index].endaddr = 0x000F7FFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F8000-0x000FFFFF
  	rdmsr(IA32_MTRR_FIX4K_F8000, &eax, &edx);
    memorytypes[index].startaddr = 0x000F8000; memorytypes[index].endaddr = 0x000F8FFF; memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000F9000; memorytypes[index].endaddr = 0x000F9FFF; memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000FA000; memorytypes[index].endaddr = 0x000FAFFF; memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000FB000; memorytypes[index].endaddr = 0x000FBFFF; memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    memorytypes[index].startaddr = 0x000FC000; memorytypes[index].endaddr = 0x000FCFFF; memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    memorytypes[index].startaddr = 0x000FD000; memorytypes[index].endaddr = 0x000FDFFF; memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    memorytypes[index].startaddr = 0x000FE000; memorytypes[index].endaddr = 0x000FEFFF; memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    memorytypes[index].startaddr = 0x000FF000; memorytypes[index].endaddr = 0x000FFFFF; memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
	       
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
        memorytypes[index].startaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL);
        memorytypes[index].endaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL) + 
					(u64) (~(vMTRR_mask & (u64)0xFFFFFFFFFFFFF000ULL) &
						paddrmask);
        memorytypes[index++].type = ((u32)vMTRR_base & (u32)0x000000FF);       
      }else{
        memorytypes[index++].invalid = 1;
      }
		}
	}

  ASSERT( index == MAX_MEMORYTYPE_ENTRIES);


  //[debug: dump the contents of memorytypes]
  //{
  //  int i;
  //  for(i=0; i < MAX_MEMORYTYPE_ENTRIES; i++){
  //    printf("\nrange  0x%016llx-0x%016llx (type=%u)", 
  //      memorytypes[i].startaddr, memorytypes[i].endaddr, memorytypes[i].type);
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
u32 vmx_getmemorytypeforphysicalpage(u64 pagebaseaddr){
 int i;
 u32 prev_type= MTRR_TYPE_RESV; 

  //check if page base address under 1M, if so used FIXED MTRRs
  if(pagebaseaddr < (1024*1024)){
    for(i=0; i < MAX_FIXED_MEMORYTYPE_ENTRIES; i++){
      if( pagebaseaddr >= memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= memorytypes[i].endaddr )
        return memorytypes[i].type;    
    }
    
    printf("\n%s: endaddr < 1M and unmatched fixed MTRR. Halt!", __FUNCTION__);
    HALT();
  }
 
  //page base address is above 1M, use VARIABLE MTRRs
  for(i= MAX_FIXED_MEMORYTYPE_ENTRIES; i < MAX_MEMORYTYPE_ENTRIES; i++){
    if( pagebaseaddr >= memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= memorytypes[i].endaddr && 
          (!memorytypes[i].invalid) ){
       if(memorytypes[i].type == MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_UC;
       }else if(memorytypes[i].type == MTRR_TYPE_WT && prev_type != MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_WT;
       }else{
        if(prev_type != MTRR_TYPE_UC && prev_type != MTRR_TYPE_WT){
          if(prev_type == MTRR_TYPE_RESV){
            prev_type = memorytypes[i].type;
          }else{
            printf("\nprev_type=%u, memorytypes=%u", prev_type, memorytypes[i].type);
            ASSERT ( prev_type == memorytypes[i].type);
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
void vmx_setupEPT(VCPU *vcpu){
  //step-1: tie in EPT PML4 structures
	//note: the default memory type (usually WB) should be determined using 
	//IA32_MTRR_DEF_TYPE_MSR. If MTRR's are not enabled (really?)
	//then all default memory is type UC (uncacheable)
  u64 *pml4_table, *pdp_table, *pd_table, *p_table;
	u32 i, j, k, paddr=0;
	
	pml4_table = (u64 *)vmx_ept_pml4_table;
	pml4_table[0] = (u64) (__hva2spa__((u32)vmx_ept_pdp_table) | 0x7); 
	
	pdp_table = (u64 *)vmx_ept_pdp_table;
		
	for(i=0; i < 4; i++){
		pdp_table[i] = (u64) ( __hva2spa__((u32)vmx_ept_pd_tables + (4096 * i)) | 0x7 );
		pd_table = (u64 *)  ((u32)vmx_ept_pd_tables + (4096 * i)) ;
		
		for(j=0; j < 512; j++){
			pd_table[j] = (u64) ( __hva2spa__((u32)vmx_ept_p_tables + (4096 * ((i*512)+j))) | 0x7 );
			p_table = (u64 *)  ((u32)vmx_ept_p_tables + (4096 * ((i*512)+j))) ;
			
			for(k=0; k < 512; k++){
 	 		 u32 memorytype = vmx_getmemorytypeforphysicalpage((u64)paddr);
       p_table[k] = (u64) (paddr)  | ((u64)memorytype << 3) | (u64)0x7 ;
       
 				/*if(paddr <= 0x0009ffff)
			 		p_table[k] = (u64) (paddr | 0x37 | 0x00);	//type 6 (WB)
	 		 	else if(paddr >= 0x000a0000 && paddr <= 0x000dffff)
	 		 		p_table[k] = (u64) (paddr | 0x07 | 0x00);	//type 0 (UC)
	 		 	else if(paddr >= 0x000e0000 && paddr <= 0x000e3fff)
	 		 		p_table[k] = (u64) (paddr | 0x2F | 0x00);	//type 5 (WP)
	 		 	else if(paddr >= 0x000e4000 && paddr <= 0x000e7fff)
	 		 		p_table[k] = (u64) (paddr | 0x27 | 0x00);	//type 4 (WT)
	 		 	else if(paddr >= 0x000e8000 && paddr <= 0x000ebfff)
	 		 		p_table[k] = (u64) (paddr | 0x2F | 0x00);	//type 5 (WP)
	 		 	else if(paddr >= 0x000ec000 && paddr <= 0x000effff)
	 		 		p_table[k] = (u64) (paddr | 0x27 | 0x00);	//type 4 (WT)
	 		 	else if(paddr >= 0x000f0000 && paddr <= 0x000fffff)
	 		 		p_table[k] = (u64) (paddr | 0x2F | 0x00);	//type 5 (WP)
	 		 	else if(paddr >= 0xbf800000 && paddr <= 0xffffffff)
	 		 		p_table[k] = (u64) (paddr | 0x07 | 0x00);	//type 0 (UC)
	 		 	else	//0x00100000 - 0xbf7fffff
			 		p_table[k] = (u64) (paddr | 0x37 | 0x00);	//type 6 (WB)*/

       	
			 paddr += 4096;
			}
		}
	}
}

