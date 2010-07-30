//------------------------------------------------------------------------------
// hardware_paging.c
//
// intel vt-x hypervisor memory isolation using extended
// page tables
//
// author: amit vasudevan (amitvasudevan@acm.org)

#include <types.h>
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <machine.h>
#include <error.h>
#include <hardware_paging.h>



//setup EPTs (page walk length 4)
//PML4 table -> PDP table -> PD table -> P table

/*
	PML4 table is 4K in length, 512 entries each 64 bits
	PML4 entry format:
	Bit
  Position(s)  Contents
	0 					 Read access; indicates whether reads are allowed from the 512-GByte region
							 controlled by this entry
	1 					 Write access; indicates whether writes are allowed to the 512-GByte region
							 controlled by this entry
	2 					 Execute access; indicates whether instruction fetches are allowed from the 512-
							 GByte region controlled by this entry
	7:3 				 Reserved (must be 0)
	11:8 			   Ignored
	N–1:12 			 Physical address of 4-KByte aligned EPT page-directory-pointer table referenced
							 by this entry
	51:N 				 Reserved (must be 0)
	63:52 			 Ignored

	PDP table is 4K in length, 512 entries each 64 bits
	PDP entry format :
	Bit
	Position(s)	 Contents
	0 					 Read access; indicates whether reads are allowed from the 1-GByte region
							 controlled by this entry
	1 					 Write access; indicates whether writes are allowed to the 1-GByte region
							 controlled by this entry
	2 					 Execute access; indicates whether instruction fetches are allowed from the 1-
							 GByte region controlled by this entry
	7:3 				 Reserved (must be 0)
	11:8 				 Ignored
	N–1:12 			 Physical address of 4-KByte aligned EPT page directory referenced by this entry1
	51:N 				 Reserved (must be 0)
	63:52 			 Ignored

	PD table is 4K in length, 512 entries each 64 bits
	PD entry format (2M pages):
	Bit
	Position(s)	 Contents
	0 					 Read access; indicates whether reads are allowed from the 2-MByte page
							 referenced by this entry
	1 					 Write access; indicates whether writes are allowed to the 2-MByte page
							 referenced by this entry
	2 					 Execute access; indicates whether instruction fetches are allowed from the 2-
							 MByte page referenced by this entry
	5:3 				 EPT memory type for this 2-MByte page (see Section 25.2.4)
	6 					 Ignore PAT memory type for this 2-MByte page (see Section 25.2.4)
	7 					 Must be 1 (otherwise, this entry references an EPT page table)
	11:8 				 Ignored
	20:12 			 Reserved (must be 0)
	N–1:21 			 Physical address of the 2-MByte page referenced by this entry
	51:N 				 Reserved (must be 0)
	63:52 			 Ignored		

	PD table is 4K in length, 512 entries each 64 bits
	PD entry format (4K pages):

	Bit
	Position(s)	 Contents
	0 					 Read access; indicates whether reads are allowed from the 2-MByte region
							 controlled by this entry
	1 					 Write access; indicates whether writes are allowed to the 2-MByte region
							 controlled by this entry
	2 					 Execute access; indicates whether instruction fetches are allowed from the 2-
							 MByte region controlled by this entry
	6:3 				 Reserved (must be 0)
	7 					 Must be 0 (otherwise, this entry maps a 2-MByte page)
	11:8 			   Ignored
	N–1:12 			 Physical address of 4-KByte aligned EPT page table referenced by this entry1
	51:N 				 Reserved (must be 0)
	63:52 			 Ignored

	P table is 4K in length, 512 entries each 64 bits
	P entry format:

	Bit
	Position(s)  Contents
	0 					 Read access; indicates whether reads are allowed from the 4-KByte page
							 referenced by this entry
	1 					 Write access; indicates whether writes are allowed to the 4-KByte page
							 referenced by this entry
	2 					 Execute access; indicates whether instruction fetches are allowed from the 4-
							 KByte page referenced by this entry
	5:3 				 EPT memory type for this 4-KByte page (see Section 25.2.4)
	6 					 Ignore PAT memory type for this 4-KByte page (see Section 25.2.4)
	11:7 				 Ignored	
	N–1:12 			 Physical address of the 4-KByte page referenced by this entry1
	51:N 				 Reserved (must be 0)
	63:52 			 Ignored
*/

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

void vmx_setupEPT(void){
	u64 *pml4_table, *pdp_table, *pd_table, *p_table;
	u32 i, j, k, paddr=0;
	
	pml4_table = (u64 *)__ept_pml4_table;
	pml4_table[0] = (u64) ((u32)__ept_pdp_table | 0x7); 
	
	pdp_table = (u64 *)__ept_pdp_table;
		
	for(i=0; i < 4; i++){
		pdp_table[i] = (u64) ( ((u32)__ept_pd_tables + (4096 * i)) | 0x7 );
		pd_table = (u64 *)  ((u32)__ept_pd_tables + (4096 * i)) ;
		
		for(j=0; j < 512; j++){
			//pd_table[j] = (u64) (paddr | 0xB7);
			//paddr += (2*1024*1024);
			pd_table[j] = (u64) ( ((u32)__ept_p_tables + (4096 * ((i*512)+j))) | 0x7 );
			p_table = (u64 *)  ((u32)__ept_p_tables + (4096 * ((i*512)+j))) ;
			
			for(k=0; k < 512; k++){
				if(paddr <= 0x0009ffff)
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
			 		p_table[k] = (u64) (paddr | 0x37 | 0x00);	//type 6 (WB)


			 paddr += (4096);
			}
		}
	}
	
	//DEBUG
	{
		//u64 *table;
		//u32 i;
		//printf("\nEPT page table dump:\n");
		//printf("\nPML4T=0x%08x, PDPT=0x%08x, PDTABLES=0x%08x, PTABLES=0x%08x",
		//	(u32)__ept_pml4_table, (u32)__ept_pdp_table, (u32)__ept_pd_tables,
		//		(u32)__ept_p_tables);
		
		//printf("\nPDTABLES dump:");
		//table = (u64 *) __ept_pd_tables;
		//for(i=0; i < 2048; i++)
		//	printf("\nindex=%u, contents=0x%016llx", (unsigned int)i, table[i]);
		
		//printf("\nPTABLES dump:");
		//table = (u64 *) __ept_p_tables;
		//for(i=0; i < (512*2048); i++)
		//	printf("\nindex=%u, contents=0x%016llx", (unsigned int)i, table[i]);
		
	}
	
	//HALT();
}

#define	IA32_MTRRCAP	0x000000fe
#define IA32_MTRR_DEF_TYPE 	0x000002ff

//fixed range MTRRs
#define IA32_MTRR_FIX64K_00000	0x00000250	//64-bits, 8 ranges (8bits/range) from 00000-7FFFF
#define IA32_MTRR_FIX16K_80000	0x00000258	//64-bits, 8 ranges (8bits/range) from 80000-9FFFF
#define IA32_MTRR_FIX16K_A0000	0x00000259	//64-bits, 8 ranges (8bits/range) from A0000-BFFFF
#define IA32_MTRR_FIX4K_C0000		0x00000268	//64-bits, 8 ranges (8bits/range) from C0000-C7FFF
#define IA32_MTRR_FIX4K_C8000		0x00000269	//64-bits, 8 ranges (8bits/range) from C8000-CFFFF
#define IA32_MTRR_FIX4K_D0000		0x0000026a	//64-bits, 8 ranges (8bits/range) from D0000-D7FFF
#define IA32_MTRR_FIX4K_D8000		0x0000026b	//64-bits, 8 ranges (8bits/range) from D8000-DFFFF
#define IA32_MTRR_FIX4K_E0000		0x0000026c	//64-bits, 8 ranges (8bits/range) from E0000-E7FFF
#define IA32_MTRR_FIX4K_E8000		0x0000026d	//64-bits, 8 ranges (8bits/range) from E8000-EFFFF
#define IA32_MTRR_FIX4K_F0000		0x0000026e	//64-bits, 8 ranges (8bits/range) from F0000-F7FFF
#define IA32_MTRR_FIX4K_F8000		0x0000026f	//64-bits, 8 ranges (8bits/range) from F8000-FFFFF

//variable range MTRRs
#define IA32_MTRR_PHYSBASE0			0x00000200
#define IA32_MTRR_PHYSMASK0			0x00000201
#define IA32_MTRR_PHYSBASE1			0x00000202
#define IA32_MTRR_PHYSMASK1			0x00000203
#define IA32_MTRR_PHYSBASE2			0x00000204
#define IA32_MTRR_PHYSMASK2			0x00000205
#define IA32_MTRR_PHYSBASE3			0x00000206
#define IA32_MTRR_PHYSMASK3			0x00000207
#define IA32_MTRR_PHYSBASE4			0x00000208
#define IA32_MTRR_PHYSMASK4			0x00000209
#define IA32_MTRR_PHYSBASE5			0x0000020a
#define IA32_MTRR_PHYSMASK5			0x0000020b
#define IA32_MTRR_PHYSBASE6			0x0000020c
#define IA32_MTRR_PHYSMASK6			0x0000020d
#define IA32_MTRR_PHYSBASE7			0x0000020e
#define IA32_MTRR_PHYSMASK7			0x0000020f


/*
	MTRR encodings:
	Uncacheable (UC)		00H
	Write Combining (WC)	01H
	Reserved*	02H
	Reserved* 03H
	Write-through (WT) 04H
	Write-protected (WP) 05H
	Writeback (WB) 06H
	Reserved* 7H through FFH
*/

void dumpmtrr(void){
	u32 eax, ebx, ecx, edx;
	//check MTRR support
	eax=0x00000001;
	ecx=0x00000000;
	asm volatile ("cpuid\r\n"
          :"=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
          :"a"(eax), "c" (ecx));
	if( !(edx & (u32)(1 << 12)) ){
		printf("\n%s: CPU does not support MTRRs!", __FUNCTION__);
		HALT();
	}

	//check MTRR caps
	rdmsr(IA32_MTRRCAP, &eax, &edx);
	printf("\nIA32_MTRRCAP: VCNT=%u, FIX=%u, WC=%u, SMRR=%u",
		(u8)eax, ((eax & (1 << 8)) >> 8),  ((eax & (1 << 10)) >> 10),
			((eax & (1 << 11)) >> 11));
	//we need VCNT=8, FIX=1
	ASSERT( ((eax & (u32)0x000000FF) == 0x8) && ((eax & (1 << 8)) >> 8) );
	
	//dump memory type of all other physical memory regions
	rdmsr(IA32_MTRR_DEF_TYPE, &eax, &edx);
	printf("\nIA32_MTRR_DEF_TYPE: type=%u, FE=%u, E=%u",
		(u8)eax, ((eax & (1 << 10)) >> 10), ((eax & (1 << 11)) >> 11) );
	//we need FE=1, E=1
	ASSERT( ((eax & (1 << 10)) >> 10) && ((eax & (1 << 11)) >> 11) );
	
	//dump fixed range MTRRs
	rdmsr(IA32_MTRR_FIX64K_00000, &eax, &edx);
	printf("\nRange 0x00000000-0x0000FFFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x00010000-0x0001FFFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x00020000-0x0002FFFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x00030000-0x0003FFFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x00040000-0x0004FFFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x00050000-0x0005FFFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x00060000-0x0006FFFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x00070000-0x0007FFFF, type=%u", ((edx & 0xFF000000) >> 24));
	rdmsr(IA32_MTRR_FIX16K_80000, &eax, &edx);
	printf("\nRange 0x00080000-0x00083FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x00084000-0x00087FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x00088000-0x0008BFFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x0008C000-0x0008FFFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x00090000-0x00093FFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x00094000-0x00097FFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x00098000-0x0009BFFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x0009C000-0x0009FFFF, type=%u", ((edx & 0xFF000000) >> 24));
	rdmsr(IA32_MTRR_FIX16K_A0000, &eax, &edx);
	printf("\nRange 0x000A0000-0x000A3FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000A4000-0x000A7FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000A8000-0x000ABFFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000AC000-0x000AFFFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000B0000-0x000B3FFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000B4000-0x000B7FFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000B8000-0x000BBFFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000BC000-0x000BFFFF, type=%u", ((edx & 0xFF000000) >> 24));

	rdmsr(IA32_MTRR_FIX4K_C0000, &eax, &edx);
	printf("\nRange 0x000C0000-0x000C0FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000C1000-0x000C1FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000C2000-0x000C2FFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000C3000-0x000C3FFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000C4000-0x000C4FFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000C5000-0x000C5FFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000C6000-0x000C6FFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000C7000-0x000C7FFF, type=%u", ((edx & 0xFF000000) >> 24));
	rdmsr(IA32_MTRR_FIX4K_C8000, &eax, &edx);
	printf("\nRange 0x000C8000-0x000C8FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000C9000-0x000C9FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000CA000-0x000CAFFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000CB000-0x000CBFFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000CC000-0x000CCFFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000CD000-0x000CDFFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000CE000-0x000CEFFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000CF000-0x000CFFFF, type=%u", ((edx & 0xFF000000) >> 24));

	rdmsr(IA32_MTRR_FIX4K_D0000, &eax, &edx);
	printf("\nRange 0x000D0000-0x000D0FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000D1000-0x000D1FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000D2000-0x000D2FFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000D3000-0x000D3FFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000D4000-0x000D4FFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000D5000-0x000D5FFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000D6000-0x000D6FFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000D7000-0x000D7FFF, type=%u", ((edx & 0xFF000000) >> 24));
	rdmsr(IA32_MTRR_FIX4K_D8000, &eax, &edx);
	printf("\nRange 0x000D8000-0x000D8FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000D9000-0x000D9FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000DA000-0x000DAFFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000DB000-0x000DBFFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000DC000-0x000DCFFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000DD000-0x000DDFFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000DE000-0x000DEFFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000DF000-0x000DFFFF, type=%u", ((edx & 0xFF000000) >> 24));

	rdmsr(IA32_MTRR_FIX4K_E0000, &eax, &edx);
	printf("\nRange 0x000E0000-0x000E0FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000E1000-0x000E1FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000E2000-0x000E2FFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000E3000-0x000E3FFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000E4000-0x000E4FFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000E5000-0x000E5FFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000E6000-0x000E6FFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000E7000-0x000E7FFF, type=%u", ((edx & 0xFF000000) >> 24));
	rdmsr(IA32_MTRR_FIX4K_E8000, &eax, &edx);
	printf("\nRange 0x000E8000-0x000E8FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000E9000-0x000E9FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000EA000-0x000EAFFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000EB000-0x000EBFFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000EC000-0x000ECFFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000ED000-0x000EDFFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000EE000-0x000EEFFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000EF000-0x000EFFFF, type=%u", ((edx & 0xFF000000) >> 24));
				
	rdmsr(IA32_MTRR_FIX4K_F0000, &eax, &edx);
	printf("\nRange 0x000F0000-0x000F0FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000F1000-0x000F1FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000F2000-0x000F2FFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000F3000-0x000F3FFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000F4000-0x000F4FFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000F5000-0x000F5FFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000F6000-0x000F6FFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000F7000-0x000F7FFF, type=%u", ((edx & 0xFF000000) >> 24));
	rdmsr(IA32_MTRR_FIX4K_F8000, &eax, &edx);
	printf("\nRange 0x000F8000-0x000F8FFF, type=%u", ((eax & 0x000000FF) >> 0));
	printf("\nRange 0x000F9000-0x000F9FFF, type=%u", ((eax & 0x0000FF00) >> 8));
	printf("\nRange 0x000FA000-0x000FAFFF, type=%u", ((eax & 0x00FF0000) >> 16));
	printf("\nRange 0x000FB000-0x000FBFFF, type=%u", ((eax & 0xFF000000) >> 24));
	printf("\nRange 0x000FC000-0x000FCFFF, type=%u", ((edx & 0x000000FF) >> 0));
	printf("\nRange 0x000FD000-0x000FDFFF, type=%u", ((edx & 0x0000FF00) >> 8));
	printf("\nRange 0x000FE000-0x000FEFFF, type=%u", ((edx & 0x00FF0000) >> 16));
	printf("\nRange 0x000FF000-0x000FFFFF, type=%u", ((edx & 0xFF000000) >> 24));
					
	printf("\nVariable MTRRs:");
	//dump variable range MTRRs
	{
		u64 paddrmask = 0x0000000FFFFFFFFFULL; //36-bits physical address
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
			if( (vMTRR_mask & ((u64)1 << 11)) )
				printf("\nVRange%u: 0x%016llx-0x%016llx, type=%u", i, 
					(vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL),
					(vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL) + 
					(u64) (~(vMTRR_mask & (u64)0xFFFFFFFFFFFFF000ULL) &
						paddrmask),
					(u8)vMTRR_base);
			else
				printf("\nVRange%u: unused", i);
		}
	}
	
	HALT();

}
