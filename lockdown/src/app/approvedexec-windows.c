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

//======================================================================
//approvedexec_windows.c
//implements windows OS specific approved execution in the trusted 
//environment in lockdown
//author(s): amit vasudevan (amitvasudevan@acm.org)
//======================================================================

#include <xmhf.h>

#include <lockdown.h>

//----------------------------------------------------------------------
//gets the physical address of a virtual address "vaddr"
//return 0xFFFFFFFF on virtual address not mapped else 
//return physical address
//assumption: the vaddr that is passed to us is a fully qualified vaddr,
//in other words if paging is disabled, then the vaddr is the 
//CS.base + offset
u32 windows_getphysicaladdress(VCPU *vcpu, u32 vaddr){
	if( (vcpu->vmcs.guest_CR0 & CR0_PE) &&
			(vcpu->vmcs.guest_CR0 & CR0_PG) ){	
		//protected mode and paging enabled, so walk guest page tables
		return (u32)(u32 *)emhf_smpguest_walk_pagetables(vcpu, vaddr);
	}else{	//paging is disabled
		return vaddr;
	}
}

//----------------------------------------------------------------------
//gets the current virtual address of the program counter
u32 windows_getpcvirtualaddress(VCPU *vcpu){
	return (u32)vcpu->vmcs.guest_CS_base + (u32)vcpu->vmcs.guest_RIP;
}


//----------------------------------------------------------------------
//scan for a valid MZ/PE header encompassing the given virtual adress
//return: image base (virtual address) on success, 0xFFFFFFFF on failure
#define SKIPMEM						(0x00400000)
#define SCANMZPE_MAXPESIZE			(4*1024*1024) 						//4MB max PE size
#define SCANMZPE_MAXPEHEADEROFFSET	0x300								//maximum distance we go until 
																		//we find a PE from a MZ
u32 windows_scanmzpe(VCPU *vcpu, u32 vaddr, 
	image_nt_headers32_t **storeNtHeader){
	
	u32 paligned_vaddr;
	u32 start_addr;
	u32 end_addr;

	u32 i_addr;

	image_dos_header_t *dosHeader;
	u32 dosHeader_paddr;
	image_nt_headers32_t *ntHeader;
	u32 ntHeader_paddr;

	(void)storeNtHeader;
	(void)vcpu;
	
	//page-align virtual address
	paligned_vaddr=PAGE_ALIGN_4K(vaddr);
	
	//compute the virtual range we will be checking within
	if(paligned_vaddr > (SKIPMEM+SCANMZPE_MAXPESIZE)){
		start_addr = paligned_vaddr - SCANMZPE_MAXPESIZE;
		end_addr = paligned_vaddr;
	}else{
		start_addr= SKIPMEM;
		end_addr = SCANMZPE_MAXPESIZE;
	}

	//printf("\n%s: start=0x%08x, end=0x%08x", __FUNCTION__, 
	//	start_addr, end_addr);

	//search for a valid PE header in the virtual range computed
	for(i_addr=start_addr; i_addr < end_addr; i_addr+=PAGE_SIZE_4K){
		dosHeader_paddr = windows_getphysicaladdress(vcpu, i_addr);
		if(dosHeader_paddr > 0x00100000 && dosHeader_paddr < (LDN_ENV_PHYSICALMEMORYLIMIT - sizeof(image_dos_header_t) - 1)){
			dosHeader=(image_dos_header_t *)gpa2hva(dosHeader_paddr);
			
			if((u16)dosHeader->e_magic == (u16)IMAGE_DOS_SIGNATURE){
				//printf("\nprobable dos header at: 0x%08X, e_lfanew=0x%08X", i_addr, dosHeader->e_lfanew);
				if((u32)dosHeader->e_lfanew < (u32)SCANMZPE_MAXPEHEADEROFFSET){			
					ntHeader_paddr = windows_getphysicaladdress(vcpu, i_addr + (u32)dosHeader->e_lfanew);
					
					if(ntHeader_paddr > 0x00100000 && ntHeader_paddr < LDN_ENV_PHYSICALMEMORYLIMIT){
						ntHeader= (image_nt_headers32_t *)gpa2hva(ntHeader_paddr);
						
						//sanity check: check if complete NT Headers is within the physical page
						//if( (u32)dosHeader->e_lfanew + sizeof(image_nt_headers32_t) > 4096)
							//printf("\nNT Headers are not contained within a single physical page..may get undefined behavior");
						
						if(ntHeader->Signature == IMAGE_NT_SIGNATURE){
							//addr is the imagebase of the PE, to that we add imagesize found in nt headers and see
							//if vaddr falls within it, if so the page belongs to this PE 
							//printf("\nPE Imagebase=0x%08X, SizeOfImage=0x%08X, Page Vaddr=0x%08X",
							//	i_addr, ntHeader->OptionalHeader.SizeOfImage, vaddr);
							if( vaddr >= i_addr && vaddr <= (i_addr+ntHeader->OptionalHeader.SizeOfImage) ){
								*storeNtHeader=ntHeader;
								return i_addr;
							}else{
								//printf("\nfound PE header, but page not within PE image!");
								return (u32)0xFFFFFFFF;
							}
						}
					}
				}
			} 
		}
	}

	//printf("\nwindows_scanmzpe: error exit, scanned until maximum of 0x%08X bytes", end_addr);
	return (u32)0xFFFFFFFF;
}


//----------------------------------------------------------------------
//PE (un)relocation routines
typedef struct {
	u32 offset : 12;
	u32 type : 4;
} reloctypeoffset_t;

#define MAX_RELOCATIONINFOSIZE	(0x20000)
u8 relocationInfo[MAX_RELOCATIONINFOSIZE];


#define	UNRELOC_SUCCESS_UNRELOCATED							0x0
#define UNRELOC_SUCCESS_NOUNRELOCATIONNEEDED				0x1
#define	UNRELOC_SUCCESS										0x2
#define UNRELOC_ERR_UNHANDLEDTYPE							0x3
#define UNRELOC_ERR_SECTIONNOTINMEM							0x4
#define	UNRELOC_ERR_SECTIONNOTONPAGEBOUNDARY				0x5
#define	UNRELOC_ERR_IMAGEBASE								0x6
#define	UNRELOC_ERR_BUFEXCEEDED								0x7
#define UNRELOC_ERR_ZEROBLOCK								0x8
#define	UNRELOC_ERR_NOPHYSMEM								0x9

u32 windows_getrelocsection(VCPU *vcpu, u32 reloc_section_va, u32 reloc_section_size, u8 *relocBuffer){
	u32 paligned_reloc_section_va;
	u32 paligned_reloc_section_va_end;
	u32 vaddr, paddr;
	u32 offset=0;
	
	AX_DEBUG(("\n  windows_getrelocsection:"));
	AX_DEBUG(("\n  reloc_section_va=0x%08x, size=0x%08x, \
		relocBuffer=0x%08x", reloc_section_va, reloc_section_size, 
		(u32)relocBuffer));
		
	paligned_reloc_section_va = PAGE_ALIGN_4K(reloc_section_va); 		//page align reloc_section_va
	paligned_reloc_section_va_end = paligned_reloc_section_va + 
		PAGE_ALIGN_4K(reloc_section_size);
	
	AX_DEBUG(("\n  paligned_reloc_section_va=0x%08x, \
		paligned_reloc_section_va_end=0x%08x", 
		paligned_reloc_section_va,
		paligned_reloc_section_va_end));

	if(paligned_reloc_section_va != reloc_section_va){
		AX_DEBUG(("\n  reloc section not on page boundary. unsupported!"));
		return UNRELOC_ERR_SECTIONNOTONPAGEBOUNDARY;
	}
	
	for(vaddr = paligned_reloc_section_va; vaddr <= paligned_reloc_section_va_end; vaddr+=PAGE_SIZE_4K){
		paddr=windows_getphysicaladdress(vcpu, vaddr);
		if(paddr >= LDN_ENV_PHYSICALMEMORYLIMIT){
			AX_DEBUG(("\n  parts of reloc section is not in memory"));
			return UNRELOC_ERR_SECTIONNOTINMEM;
		}
		
		if(vaddr == paligned_reloc_section_va_end)
			memcpy((void *)((u32)relocBuffer+offset), (void *)gpa2hva(paddr), (reloc_section_size % PAGE_SIZE_4K));
		else
			memcpy((void *)((u32)relocBuffer+offset), (void *)gpa2hva(paddr), PAGE_SIZE_4K);

		offset+=PAGE_SIZE_4K;		
	}

	
	return UNRELOC_SUCCESS;
}

u8 unrelocateBuffer[PAGE_SIZE_4K * 3];

u32 windows_unrelocatepage_processrelocations(VCPU *vcpu, u32 imagebase, u32 originalimagebase,
	void *page, image_base_relocation_t *relocEntry, u8 *relocEntry_relocInfo){
	
	u32 i;
	reloctypeoffset_t *relocTypeOffsets;
	u32 relocvalue, *relocaddr;
	
	(void)vcpu;
	
	for(i=0; i < ((relocEntry->SizeOfBlock-8)/sizeof(unsigned short int)); i++){
		relocTypeOffsets = (reloctypeoffset_t *)( (u8 *)relocEntry_relocInfo + (i*2));
		//if(vaddr == 0x8084d426)
		//	AX_DEBUG(("\nEntry %u: Type=%x, Offset=%x", i, relocTypeOffsets->type, relocTypeOffsets->offset));
		
		if(relocTypeOffsets->type == 3){
			relocvalue=	imagebase-originalimagebase;
			relocaddr = (u32 *)( (u32)page + relocTypeOffsets->offset);
			//if(vaddr == 0x8084d426)
			//	AX_DEBUG(("\nrelocaddr value, before=0x%08x,", *relocaddr));
			*relocaddr -= relocvalue;	//relocvalue would have been added to relocaddr to perform the reloc, we thus subtract to perform unrelc
			//if(vaddr == 0x8084d426)
			//	AX_DEBUG(("\nafter=0x%08x,", *relocaddr));
		}else if(relocTypeOffsets->type == 0){
			//abs reloc entry, no relocation needed		
		}else{
			AX_DEBUG(("\n unhandled relocation type %x!", relocTypeOffsets->type));
			return UNRELOC_ERR_UNHANDLEDTYPE;
		}
	}

	return UNRELOC_SUCCESS;
}



//return 0 on error, 1 on success
//u32 windows_unrelocatepage(image_nt_headers32_t *ntHeader, u32 imagebase, u32 vaddr, void *inputPage, void *outputPage){
u32 windows_unrelocatepage(VCPU *vcpu, image_nt_headers32_t *ntHeader, u32 imagebase, u32 vaddr, void *inputPagePrevious, void *inputPage, void *inputPageNext, void *outputPage){
	image_base_relocation_t *relocEntry;
	image_base_relocation_t	*relocEntryPrevious=NULL;
	image_base_relocation_t *relocEntryNext=NULL;
	u8 *relocEntry_relocInfo=NULL;
	u8 *relocEntryPrevious_relocInfo=NULL;
	u8 *relocEntryNext_relocInfo=NULL;
	u32 current_size=0;
	//u32 prev_size=0;
	u32 paligned_vaddr = PAGE_ALIGN_4K(vaddr); 
	u32 found_relocEntry=0;
	u32 reloc_size, reloc_vaddr;
	u32 originalimagebase=ntHeader->OptionalHeader.ImageBase;
	u32 retval;
	//u32 prevpage_paddr;

	u32 i;
	reloctypeoffset_t *relocTypeOffsets;
	u32 needPreviousPage=0, needNextPage=0;
	
	AX_DEBUG(("\n windows_unrelocatepage: imagebase=0x%08x, vaddr=0x%08x, paligned=0x%08x", imagebase, vaddr, paligned_vaddr));
	AX_DEBUG(("\n inputPage(prev, curr, next)=0x%08x, 0x%08x, 0x%08x", (u32)inputPagePrevious, (u32)inputPage, (u32)inputPageNext));
	
	if(imagebase < originalimagebase){
		AX_DEBUG(("\n error: imagebase < originalimagebase"));
		return UNRELOC_ERR_IMAGEBASE;
	}
	
	//get hold of .reloc section base and size
	reloc_vaddr=ntHeader->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC].VirtualAddress;
	reloc_size=ntHeader->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC].Size;

	AX_DEBUG(("\n reloc section base=0x%08X, size=0x%08X", reloc_vaddr, reloc_size));
	if(reloc_size > MAX_RELOCATIONINFOSIZE){
		AX_DEBUG(("\n error: relocsize > MAX_RELOCATIONINFOSIZE"));
		return UNRELOC_ERR_BUFEXCEEDED;
	}
	
	//get relocation information from reloc section
	memset(&relocationInfo, 0, MAX_RELOCATIONINFOSIZE);
	retval=windows_getrelocsection(vcpu, imagebase+reloc_vaddr, reloc_size, (u8 *)&relocationInfo);
	if(retval != UNRELOC_SUCCESS){
		AX_DEBUG(("\n error: unable to get relocation info!"));
		return retval;
	}
		
	//get base reloc entries for inputPage, inputPagePrevious and inputPageNext
	//what we know from the PECOFF spec is relocEntry->VirtualAddress is always page-aligned 
	//what we know from the Windows Loader is imagebase is always page-aligned
	relocEntry = (image_base_relocation_t *)relocationInfo;
	relocEntry_relocInfo = (u8 *)((u8 *)relocationInfo + 8);
	while(current_size < reloc_size){
		if(relocEntry->SizeOfBlock == 0){
			retval=UNRELOC_ERR_ZEROBLOCK;			
			break;
		}

		//AX_DEBUG(("\nEntry: Vaddr=0x%08x, Size=0x%08x", relocEntry->VirtualAddress, relocEntry->SizeOfBlock));
		if( paligned_vaddr == (relocEntry->VirtualAddress + imagebase)){
			//store correct values for relocEntryPrevious and relocEntryNext
			if(relocEntryPrevious){
				if(relocEntry->VirtualAddress - relocEntryPrevious->VirtualAddress > PAGE_SIZE_4K){
					relocEntryPrevious=NULL;
					relocEntryPrevious_relocInfo=NULL;
				}
			}

			current_size+=relocEntry->SizeOfBlock;
			if(current_size < reloc_size){
				relocEntryNext = (image_base_relocation_t *)( (u8 *)relocationInfo + current_size);
				if(relocEntryNext->SizeOfBlock){
					relocEntryNext_relocInfo = (u8 *) ((u8 *)relocationInfo + current_size + 8);
				}else{
					relocEntryNext=NULL;
					relocEntryNext_relocInfo=NULL;
				}
			}else{
				relocEntryNext=NULL;
				relocEntryNext_relocInfo=NULL;
			}

			found_relocEntry = 1;
			break;
		}
		
		relocEntryPrevious = relocEntry;
		relocEntryPrevious_relocInfo = relocEntry_relocInfo;
		current_size+=relocEntry->SizeOfBlock;
		relocEntry = (image_base_relocation_t *)( (u8 *)relocationInfo + current_size);
		relocEntry_relocInfo = (u8 *) ((u8 *)relocationInfo + current_size + 8);
	}
	
	if(!found_relocEntry){
		if(retval == UNRELOC_ERR_ZEROBLOCK)
			return UNRELOC_ERR_ZEROBLOCK;
		else
			return UNRELOC_SUCCESS_NOUNRELOCATIONNEEDED;
	}
	
	//found base relocation entry and info for inputPage
	AX_DEBUG(("\n relocEntry: rva=0x%08x, size=0x%08x", (u32)relocEntry->VirtualAddress, (u32)relocEntry->SizeOfBlock));
	if(relocEntryPrevious){
		AX_DEBUG(("\n relocEntryPrevious: rva=0x%08x, size=0x%08x", (u32)relocEntryPrevious->VirtualAddress, (u32)relocEntryPrevious->SizeOfBlock));
	}
	if(relocEntryNext){
		AX_DEBUG(("\n relocEntryNext: rva=0x%08x, size=0x%08x", (u32)relocEntryNext->VirtualAddress, (u32)relocEntryNext->SizeOfBlock));
	}
		
	memset(&unrelocateBuffer, 0, (PAGE_SIZE_4K *3));

	//determine if we need the previous page to perform a successful unrelocation
	if(relocEntryPrevious){
		for(i=0; i < ((relocEntryPrevious->SizeOfBlock-8)/sizeof(unsigned short int)); i++){
			relocTypeOffsets = (reloctypeoffset_t *)( (u8 *)relocEntryPrevious_relocInfo + (i*2));
			if(((u32)relocTypeOffsets->offset + 4) >= PAGE_SIZE_4K){
				needPreviousPage=1;
				break;
			}
		}
	
		if(needPreviousPage){
			if((u32)inputPagePrevious >= LDN_ENV_PHYSICALMEMORYLIMIT){
				AX_DEBUG(("\n Need inputPagePrevious, but is not present in guest OS!"));
				return UNRELOC_ERR_NOPHYSMEM;
			}

			AX_DEBUG(("\n Need inputPagePrevious - GOT IT!"));
			memcpy((void *)((u32)unrelocateBuffer), inputPagePrevious, PAGE_SIZE_4K);
		}
	}
		
	//copy inputPage 
	memcpy((void *)((u32)unrelocateBuffer+PAGE_SIZE_4K), inputPage, PAGE_SIZE_4K);
	
	//determine if we need the next page to perform a successful unrelocation
	if(relocEntryNext){
		for(i=0; i < ((relocEntryNext->SizeOfBlock-8)/sizeof(unsigned short int)); i++){
			relocTypeOffsets = (reloctypeoffset_t *)( (u8 *)relocEntryNext_relocInfo + (i*2));
			if(((u32)relocTypeOffsets->offset + 4) >= PAGE_SIZE_4K){
				needNextPage=1;
				break;
			}
		}
	
		if(needNextPage){
			if((u32)inputPageNext >= LDN_ENV_PHYSICALMEMORYLIMIT){
				AX_DEBUG(("\n Need inputPageNext, but is not present in guest OS!"));
				return UNRELOC_ERR_NOPHYSMEM;
			}

			AX_DEBUG(("\n Need inputPageNext - GOT IT!"));
			memcpy((void *)((u32)unrelocateBuffer+(2*PAGE_SIZE_4K)), inputPageNext, PAGE_SIZE_4K);
		}
	}


	//ok now we have unrelocateBuffer setup, perform the unrelocations
	if(needPreviousPage){
		retval = windows_unrelocatepage_processrelocations(vcpu, imagebase, 
				originalimagebase, (void *)((u32)unrelocateBuffer), relocEntryPrevious, relocEntryPrevious_relocInfo);
		if(retval != UNRELOC_SUCCESS){
			AX_DEBUG(("\n error in processing relocations for inputPagePrevious"));
			return retval;
		}
	}

	retval = windows_unrelocatepage_processrelocations(vcpu, imagebase, 
			originalimagebase, (void *)((u32)unrelocateBuffer+PAGE_SIZE_4K), relocEntry, relocEntry_relocInfo);
	if(retval != UNRELOC_SUCCESS){
		AX_DEBUG(("\n error in processing relocations for inputPage"));
		return retval;
	}

	//we dont need to perform unrelocation for inputPageNext
	
	memcpy(outputPage, (void *)((u32)unrelocateBuffer+PAGE_SIZE_4K), PAGE_SIZE_4K);
	
	return UNRELOC_SUCCESS_UNRELOCATED;
}


u8 outputPage[PAGE_SIZE_4K];

//some TODOS
//1. we need to ensure that the import address table is factored out
//of the hash comparison. the IAT lies within the code page and hence for
//those pages we need to do partial hashes
//2. we need to account for PEs whose sections are not page aligned during
//hash generation

//------------------------------------------------------------------------------
//this is the top level function which verifies the code integrity of the 
//memory page with physical address paddr under the windows OS
//return: 1 on success, 0 on failure
u32 windows_verifycodeintegrity(VCPU *vcpu, u32 paddr, u32 vaddrfromcpu){
	u32 vaddr, paligned_vaddr;
	u32 imagebase, retval;
	//u8 *p;	
	image_nt_headers32_t *ntHeader;
	//int i;
	u32 paligned_paddr;

	u32 paddr_prevpage, paddr_nextpage;
	u32 paligned_paddr_prevpage, paligned_paddr_nextpage;

	(void)vaddrfromcpu;
	
//__step1:	
	//if an instruction straddles page boundaries, the nested/extended
	//page-fault intercept can deliver a physical address that has a 
	//forward bias. for example, if the faulting paddr=0x0fff and the instruction
	//there spanned to the next page (0x1000), the fault will give us a 
	//paddr = 0x1000. however we need the page 0x0000 for hash computation
	//so we always get the virtual address and check if the lower 12 bits equal
	//the lower 12 bits of the paddr. if not, we traverse the guest paging
	//structures (if loaded) to compute the correct physical address
	vaddr = windows_getpcvirtualaddress(vcpu);
	if( (vaddr & (u32)0x00000FFF) != (paddr & (u32)0x00000FFF) ){
	 	//need to adjust paddr
	 	paddr = windows_getphysicaladdress(vcpu, vaddr);
	 	ASSERT(paddr != 0xFFFFFFFFUL);
	}
	
	AX_DEBUG(("\nstep-1: paddr=0x%08x, vaddr=0x%08x", paddr, vaddr));

	paligned_vaddr = PAGE_ALIGN_4K(vaddr);
	paligned_paddr = PAGE_ALIGN_4K(paddr);

	
//__step2:	
	//check for valid PE image if in protected mode
	if(! (vcpu->vmcs.guest_CR0 & CR0_PE) ){
		AX_DEBUG(("\nstep-2: SKIPPED - in real mode"));
		retval = 0;
		goto __step5;
	}
	
	imagebase=windows_scanmzpe(vcpu, vaddr, &ntHeader);
	
	if(imagebase == 0xFFFFFFFF){
		AX_DEBUG(("\nstep-2: SKIPPED - in protected mode, but unable to find PE image"));
		retval = 0;
		goto __step5;
	}
	
	//printf("\nSQ: imagebase=0x%08x, vaddr=0x%08x", imagebase, vaddr);
	
	AX_DEBUG(("\nstep-2: PE imagebase(load=0x%08x, orig=0x%08x), image size=0x%08x", 
		(u32)imagebase, (u32)ntHeader->OptionalHeader.ImageBase, (u32)ntHeader->OptionalHeader.SizeOfImage));

//__step3:	
	//unrelocate the memory page of the PE image if needed
	if(imagebase == ntHeader->OptionalHeader.ImageBase){
		AX_DEBUG(("\nstep-3: SKIPPED - PE image loaded at preferred adress, no relocation needed"));
		goto __step4;
	}

	paddr_prevpage = windows_getphysicaladdress(vcpu, vaddr - PAGE_SIZE_4K);
	paligned_paddr_prevpage = PAGE_ALIGN_4K(paddr_prevpage);
	if(paligned_paddr_prevpage >= LDN_ENV_PHYSICALMEMORYLIMIT)	paligned_paddr_prevpage = 0xFFFFFFFF;
	paddr_nextpage = windows_getphysicaladdress(vcpu, vaddr + PAGE_SIZE_4K);
	paligned_paddr_nextpage = PAGE_ALIGN_4K(paddr_nextpage);
	if(paligned_paddr_nextpage >= LDN_ENV_PHYSICALMEMORYLIMIT)	paligned_paddr_nextpage = 0xFFFFFFFF;
	
		
	retval=windows_unrelocatepage(vcpu, ntHeader, imagebase, vaddr, (void *)paligned_paddr_prevpage, (void *)paligned_paddr, (void *)paligned_paddr_nextpage, (void *)&outputPage);
	if(retval != UNRELOC_SUCCESS_NOUNRELOCATIONNEEDED && retval != UNRELOC_SUCCESS_UNRELOCATED){
		AX_DEBUG(("\nstep-3: ERROR - unrelocate failed, proceeding in any case"));
		retval=0;
		goto __step5;
	}
	
	if(retval == UNRELOC_SUCCESS_NOUNRELOCATIONNEEDED){
		AX_DEBUG(("\nstep-3: SUCCESS - no unrelocation needed"));
	}else{
		AX_DEBUG(("\nstep-3: SUCCESS - unrelocated memory page"));
		paligned_paddr=(u32)&outputPage;
	}
	

__step4:	

#if defined (__LDN_APPROVEDEXEC_CMPHASHES__)
	//verify the memory page conents with hash list 
	{
		u32 index, fullhash;
		retval=approvedexec_checkhashes(paligned_paddr, &index, &fullhash);

		/*if(!retval){
			printf("\nPEBase(o:a)=(0x%08x:0x%08x), UNMATCHED, p=0x%08x, v=0x%08x", 
						ntHeader->OptionalHeader.ImageBase, imagebase, 
						paddr, vaddr);
		}else{
			printf("\nPE base=0x%08x, MATCHED (%u), p=0x%08x, v=0x%08x", 
				imagebase, (1 ? fullhash : 0), PAGE_ALIGN_4K(paddr), paligned_vaddr);
				//if(fullhash)
				//	printf("\n  %s", hashlist_full[index].name);
				//else
				//	printf("\n  %s", hashlist_partial[index].name);
		}*/
	}
#endif

__step5:	
	if(retval){
		AX_DEBUG(("\nstep-4: SUCCESS - verified page contents"));
	}else{
		AX_DEBUG(("\nstep-4: ERROR - could not verify page contents"));
	}
	
	return retval;
}

