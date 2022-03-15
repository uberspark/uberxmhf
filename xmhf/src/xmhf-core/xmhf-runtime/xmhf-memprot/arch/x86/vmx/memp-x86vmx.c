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
void xmhf_memprot_arch_x86vmx_initialize(VCPU *vcpu){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);

	_vmx_gathermemorytypes(vcpu);
#ifndef __XMHF_VERIFICATION__
	_vmx_setupEPT(vcpu);
#endif

	vcpu->vmcs.control_VMX_seccpu_based |= (1 << 1); //enable EPT
	vcpu->vmcs.control_VMX_seccpu_based |= (1 << 5); //enable VPID
	vcpu->vmcs.control_vpid = 1; //VPID=0 is reserved for hypervisor
	vcpu->vmcs.control_EPT_pointer = hva2spa((void*)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E; //page walk of 4 and WB memory
	vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
	vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
}


//----------------------------------------------------------------------
// local (static) support functions follow

/*
 * Read fixed MTRRs and put them to vcpu->vmx_ept_memorytypes.
 * msraddr: ECX argument to RDMSR; e.g. IA32_MTRR_FIX64K_00000
 * pindex: start index into vcpu->vmx_ept_memorytypes
 * start: start address of the first range
 * step: size of each range (8 ranges total)
 */
static void _vmx_read_fixed_mtrr(VCPU *vcpu, u32 msraddr, u32 *pindex, u64 start, u64 step){
	u32 eax, edx, index = *pindex;
	u64 msr;
	rdmsr(msraddr, &eax, &edx);
	msr = ((u64)edx << 32) | (u64)eax;
	for (u32 i = 0; i < 8; i++) {
		struct _memorytype *memorytype = &(vcpu->vmx_ept_memorytypes[index++]);
		memorytype->startaddr = start + step * i;
		memorytype->endaddr = start + step * (i + 1) - 1;
		memorytype->type = (u32)((msr >> (i * 8)) & 0xFF);
	}
	*pindex = index;
}

//---gather memory types for system physical memory------------------------------
static void _vmx_gathermemorytypes(VCPU *vcpu){
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
  		printf("\nCPU(0x%02x): CPU does not support MTRRs!", vcpu->id);
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

	// Read MTRR default type register
	rdmsr(IA32_MTRR_DEF_TYPE, &eax, &edx);
	vcpu->vmx_ept_defaulttype = (eax & 0xFFU);
	// Sanity check that Fixed-range MTRRs are enabled
	HALT_ON_ERRORCOND(eax & (1 << 10));
	// Sanity check that MTRRs are enabled
	HALT_ON_ERRORCOND(eax & (1 << 11));

	#ifndef __XMHF_VERIFICATION__
	//1. clear memorytypes array
	memset((void *)&vcpu->vmx_ept_memorytypes, 0, sizeof(struct _memorytype) * MAX_MEMORYTYPE_ENTRIES);
	#endif


	//2. grab memory types using FIXED MTRRs
	//0x00000000-0x0007FFFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX64K_00000, &index, 0x00000000ULL, 0x00010000ULL);
	//0x00080000-0x0009FFFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX16K_80000, &index, 0x00080000ULL, 0x00004000ULL);
	//0x000A0000-0x000BFFFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX16K_A0000, &index, 0x000A0000ULL, 0x00004000ULL);
	//0x000C0000-0x000C7FFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX4K_C0000,  &index, 0x000C0000ULL, 0x00001000ULL);
	//0x000C8000-0x000C8FFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX4K_C8000,  &index, 0x000C8000ULL, 0x00001000ULL);
	//0x000D0000-0x000D7FFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX4K_D0000,  &index, 0x000D0000ULL, 0x00001000ULL);
	//0x000D8000-0x000DFFFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX4K_D8000,  &index, 0x000D8000ULL, 0x00001000ULL);
	//0x000E0000-0x000E7FFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX4K_E0000,  &index, 0x000E0000ULL, 0x00001000ULL);
	//0x000E8000-0x000EFFFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX4K_E8000,  &index, 0x000E8000ULL, 0x00001000ULL);
	//0x000F0000-0x000F7FFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX4K_F0000,  &index, 0x000F0000ULL, 0x00001000ULL);
	//0x000F8000-0x000FFFFF
	_vmx_read_fixed_mtrr(vcpu, IA32_MTRR_FIX4K_F8000,  &index, 0x000F8000ULL, 0x00001000ULL);

	HALT_ON_ERRORCOND(index == MAX_FIXED_MEMORYTYPE_ENTRIES);


	//3. grab memory types using variable length MTRRs
	{
		u32 eax, ebx, ecx, edx;
		u64 paddrmask; //mask physical address, usually 36-bits
		u64 vMTRR_base, vMTRR_mask;
		u32 msrval=IA32_MTRR_PHYSBASE0;
		u32 i;

		/* Check whether CPUID 0x80000008 is supported */
		cpuid(0x80000000U, &eax, &ebx, &ecx, &edx);
		HALT_ON_ERRORCOND(eax >= 0x80000008U)
		/* Compute paddrmask from CPUID.80000008H:EAX[7:0] (max physical addr) */
		cpuid(0x80000008U, &eax, &ebx, &ecx, &edx);
		eax &= 0xFFU;
		HALT_ON_ERRORCOND(eax >= 32 && eax <= 64);
		paddrmask = (1ULL << eax) - 1ULL;

		for(i=0; i < num_vmtrrs; i++){
			rdmsr(msrval, &eax, &edx);
			vMTRR_base = ((u64)edx << 32) | (u64)eax;
			msrval++;
			rdmsr(msrval, &eax, &edx);
			vMTRR_mask = ((u64)edx << 32) | (u64)eax;
			msrval++;
			if( (vMTRR_mask & ((u64)1 << 11)) ){
				u64 baseaddr = (vMTRR_base & ~((u64)PAGE_SIZE_4K - 1));
				u64 maskaddr = (vMTRR_mask & ~((u64)PAGE_SIZE_4K - 1));
				/* Make sure base and mask do not exceed physical address */
				HALT_ON_ERRORCOND(!(~paddrmask & baseaddr));
				HALT_ON_ERRORCOND(!(~paddrmask & maskaddr));
				/* Make sure mask is of the form 0b111...111000...000 */
				HALT_ON_ERRORCOND(!(((paddrmask & ~maskaddr) + 1) &
									(paddrmask & ~maskaddr)));
				vcpu->vmx_ept_memorytypes[index].startaddr = baseaddr;
				vcpu->vmx_ept_memorytypes[index].endaddr = baseaddr + (~maskaddr & paddrmask);
				vcpu->vmx_ept_memorytypes[index++].type = ((u32)vMTRR_base & 0xFFU);
			}else{
				vcpu->vmx_ept_memorytypes[index++].invalid = 1;
			}
		}
	}

	printf("\n%s: gathered MTRR details, number of entries=%u", __FUNCTION__, index);
	HALT_ON_ERRORCOND( index <= (MAX_MEMORYTYPE_ENTRIES+1) );

  //[debug: dump the contents of vcpu->vmx_ept_memorytypes]
  //{
  //  int i;
  //  for(i=0; i < MAX_MEMORYTYPE_ENTRIES; i++){
  //    printf("\nrange  0x%016llx-0x%016llx (type=%u)",
  //      vcpu->vmx_ept_memorytypes[i].startaddr, vcpu->vmx_ept_memorytypes[i].endaddr, vcpu->vmx_ept_memorytypes[i].type);
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
            HALT_ON_ERRORCOND ( prev_type == vcpu->vmx_ept_memorytypes[i].type);
          }
        }
       }
    }
  }

  if(prev_type == MTRR_TYPE_RESV)
    prev_type = vcpu->vmx_ept_defaulttype;

  return prev_type;
}


//---setup EPT for VMX----------------------------------------------------------
#ifdef __AMD64__
static void _vmx_setupEPT(VCPU *vcpu){
	//step-1: tie in EPT PML4 structures
	u64 *pml4_entry = (u64 *)vcpu->vmx_vaddr_ept_pml4_table;
	u64 *pdp_entry = (u64 *)vcpu->vmx_vaddr_ept_pdp_table;
	u64 *pd_entry = (u64 *)vcpu->vmx_vaddr_ept_pd_tables;
	u64 *p_entry = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
	u64 pdp_table = hva2spa((void*)vcpu->vmx_vaddr_ept_pdp_table);
	u64 pd_table = hva2spa((void*)vcpu->vmx_vaddr_ept_pd_tables);
	u64 p_table = hva2spa((void*)vcpu->vmx_vaddr_ept_p_tables);
	// TODO: for x86_64, likely can use 1G / 2M pages.
	// If so, also need to change _vmx_getmemorytypeforphysicalpage()

	for (u64 paddr = 0; paddr < MAX_PHYS_ADDR; paddr += PAGE_SIZE_4K) {
		if (PAGE_ALIGNED_512G(paddr)) {
			/* Create PML4E */
			u64 i = paddr / PAGE_SIZE_512G;
			pml4_entry[i] = (pdp_table + i * PAGE_SIZE_4K) | 0x7;
		}
		if (PAGE_ALIGNED_1G(paddr)) {
			/* Create PDPE */
			u64 i = paddr / PAGE_SIZE_1G;
			pdp_entry[i] = (pd_table + i * PAGE_SIZE_4K) | 0x7;
		}
		if (PAGE_ALIGNED_2M(paddr)) {
			/* Create PDE */
			u64 i = paddr / PAGE_SIZE_2M;
			pd_entry[i] = (p_table + i * PAGE_SIZE_4K) | 0x7;
		}
		/* PAGE_ALIGNED_4K */
		{
			/* Create PE */
			u64 i = paddr / PAGE_SIZE_4K;
			u64 memorytype = _vmx_getmemorytypeforphysicalpage(vcpu, paddr);
			u64 lower;
			/*
			 * For memorytype equal to 0 (UC), 1 (WC), 4 (WT), 5 (WP), 6 (WB),
			 * MTRR memory type and EPT memory type are the same encoding.
			 * Currently other encodings are reserved.
			 */
			HALT_ON_ERRORCOND(memorytype == 0 || memorytype == 1 ||
								memorytype == 4 || memorytype == 5 ||
								memorytype == 6);
			if ((paddr >= (rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M)) &&
				(paddr < (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize))) {
				lower = 0x0;	/* not present */
			} else {
				lower = 0x7;	/* present */
			}
			p_entry[i] = paddr | (memorytype << 3) | lower;
		}
	}
}
#else /* !__AMD64__ */
static void _vmx_setupEPT(VCPU *vcpu){
	//step-1: tie in EPT PML4 structures
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
				/*
				 * For memorytype equal to 0 (UC), 1 (WC), 4 (WT), 5 (WP), 6 (WB),
				 * MTRR memory type and EPT memory type are the same encoding.
				 * Currently other encodings are reserved.
				 */
				HALT_ON_ERRORCOND(memorytype == 0 || memorytype == 1 ||
									memorytype == 4 || memorytype == 5 ||
									memorytype == 6);
				//the XMHF memory region includes the secure loader +
				//the runtime (core + app). this runs from
				//(rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M) with a size
				//of (rpb->XtVmmRuntimeSize+PAGE_SIZE_2M)
				//make XMHF physical pages inaccessible
				if( (paddr >= (rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M)) &&
					(paddr < (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize)) ){
					p_table[k] = (u64) (paddr) | ((u64)memorytype << 3) | (u64)0x0 ;	//not-present
				}else{
					p_table[k] = (u64) (paddr) | ((u64)memorytype << 3) | (u64)0x7 ;	//present
				}

				paddr += PAGE_SIZE_4K;
			}
		}
	}
}
#endif /* __AMD64__ */


//flush hardware page table mappings (TLB)
void xmhf_memprot_arch_x86vmx_flushmappings(VCPU *vcpu){
  __vmx_invept(VMX_INVEPT_SINGLECONTEXT,
          (u64)vcpu->vmcs.control_EPT_pointer);
}

//flush hardware page table mappings (TLB)
void xmhf_memprot_arch_x86vmx_flushmappings_localtlb(VCPU *vcpu){
	(void)vcpu;
  __vmx_invept(VMX_INVEPT_GLOBAL,
          (u64)0);
}

//set protection for a given physical memory address
void xmhf_memprot_arch_x86vmx_setprot(VCPU *vcpu, u64 gpa, u32 prottype){
  u32 pfn;
  u64 *pt;
  u32 flags =0;

#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
   	assert ( (vcpu != NULL) );
	assert ( ( (gpa < rpb->XtVmmRuntimePhysBase) ||
							 (gpa >= (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize))
						   ) );
	assert ( ( (prottype > 0)	&&
	                         (prottype <= MEMP_PROT_MAXVALUE)
	                       ) );
	assert (
	 (prottype == MEMP_PROT_NOTPRESENT) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READONLY) && (prottype & MEMP_PROT_EXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READWRITE) && (prottype & MEMP_PROT_EXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READONLY) && (prottype & MEMP_PROT_NOEXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READWRITE) && (prottype & MEMP_PROT_NOEXECUTE))
	);
#endif

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
u32 xmhf_memprot_arch_x86vmx_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
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

u64 xmhf_memprot_arch_x86vmx_get_EPTP(VCPU *vcpu)
{
  HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
  return vcpu->vmcs.control_EPT_pointer;
}
void xmhf_memprot_arch_x86vmx_set_EPTP(VCPU *vcpu, u64 eptp)
{
  HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
  vcpu->vmcs.control_EPT_pointer = eptp;
}
