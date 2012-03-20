//windows.c
//implements windows OS specific approved execution in the trusted environment in lockdown
//author(s): amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h>

#include <lockdown.h>

#include <approvedexec.h>
#include <exe_pe.h>
//#include <sha1.h>


#if 0
//windows: current corner cases for implmentation
//1. wrkx86.exe: INIT section, overwrites parts of itself 
//0x001e9000-0x00216000 = rva of INIT
//2. trampoline page (not sure whats happening there, guess some syscall/dpc stub?)
//returns:1 if the specified vaddr falls in a corner case else 0
#define	NTKERNEL_LOADIMAGEBASE	0x80800000	//nt kernel is always loaded at this vaddr
#define CORNERCASE_1_VADDRSTART	(NTKERNEL_LOADIMAGEBASE + 0x001e9000)
#define CORNERCASE_1_VADDREND		(NTKERNEL_LOADIMAGEBASE + 0x00216000)
#define	CORNERCASE_2_VADDRSTART	(0x81711000)
#define CORNERCASE_2_VADDREND		(0x81712000)
u32 windows_unrelocate_cornercases(u32 vaddr){
	if(vaddr >= CORNERCASE_1_VADDRSTART && vaddr < CORNERCASE_1_VADDREND)
		return 1;
	if(vaddr >= CORNERCASE_2_VADDRSTART && vaddr < CORNERCASE_2_VADDREND)
		return 1;

	return 0;
}
#endif

//------------------------------------------------------------------------------
//gets the physical address of a virtual address vaddr
//return 0xFFFFFFFF on virtual address not mapped else return physical address
//assumption: the vaddr that is passed to us is a fully qualified vaddr,
//in other words if paging is disabled, then the vaddr is the Cs.base + offset
u32 windows_getphysicaladdress(VCPU *vcpu, u32 vaddr){
//if(vcpu->guest_unrestricted){
	if( (vcpu->vmcs.guest_CR0 & CR0_PE) &&
			(vcpu->vmcs.guest_CR0 & CR0_PG) ){	
		//protected mode and paging enabled, so walk guest page tables
		return (u32)(u32 *)emhf_smpguest_walk_pagetables(vcpu, vaddr);
	}else{	//paging is disabled
		return vaddr;
	}

/*}else{
	if( (vcpu->guest_currentstate & GSTATE_PROTECTEDMODE) &&
			(vcpu->guest_currentstate & GSTATE_PROTECTEDMODE_PG) ){	
		//protected mode and paging enabled, so walk guest page tables
		return emhf_guestpgtbl_walk(vcpu, vaddr);
	}else{	//paging is disabled
		return vaddr;
	}
}*/
}

//------------------------------------------------------------------------------
//gets the virtual address of the physical address paddr
u32 windows_getvirtualaddress(VCPU *vcpu, u32 paddr){
	(void)paddr;
	//if( (vcpu->guest_currentstate & GSTATE_PROTECTEDMODE) &&
	//		(vcpu->guest_currentstate & GSTATE_PROTECTEDMODE_PG) ){	
		//protected mode and paging enabled
		//we just use a simple trick, on a NX fault which is the only time
		//this is called, guest_RIP will contain
		//the virtual address of the guest memory page causing the fault, which is
		//the virtual address we need!
	//	return (u32)vcpu->vmcs.guest_RIP;
	//}else{	//paging is disabled
		return (u32)vcpu->vmcs.guest_CS_base + (u32)vcpu->vmcs.guest_RIP;
	//}
}

#define SKIPMEM									(0x00400000)
#define SCANMZPE_MAXPESIZE			(16*1024*1024) 	//16MB max PE size
//#define	SCANMZPE_PEHEADERGRAN		(PAGE_SIZE_4K)	//header is assumed to start on this multiple always
#define SCANMZPE_MAXPEHEADEROFFSET	0x300				//maximum distance we go until we find a PE from a MZ
//scan for a valid MZ/PE header encompassing the given virtual adress
//return: image base (virtual address) on success, 0xFFFFFFFF on failure
u32 windows_scanmzpe(VCPU *vcpu, u32 vaddr, IMAGE_NT_HEADERS32 **storeNtHeader){
//u32 windows_scanmzpe(u32 vaddr){
	IMAGE_DOS_HEADER *dosHeader;
	IMAGE_NT_HEADERS32 *ntHeader;
	u32 addr, dosHeader_paddr, ntHeader_paddr, end_addr, i_addr;
	
	//addr = ((vaddr) & ~(PAGE_SIZE_4K - 1));
	addr=PAGE_ALIGN_4K(vaddr);
	
	if(addr > (SKIPMEM+SCANMZPE_MAXPESIZE))
		end_addr= addr - SCANMZPE_MAXPESIZE;
	else
		end_addr= SKIPMEM;
		
	//printf("\nwindows_scanmzpe: enter, vaddr=0x%08X, addr=0x%08X, end_addr=0x%08X", vaddr, addr, end_addr);
	
	for(i_addr=addr; i_addr > end_addr; i_addr-=4096){
		dosHeader_paddr = windows_getphysicaladdress(vcpu, i_addr);
		if(dosHeader_paddr > 0x00100000 && dosHeader_paddr < LDN_ENV_PHYSICALMEMORYLIMIT){
			dosHeader=(IMAGE_DOS_HEADER *)dosHeader_paddr;
			
			if((u16)dosHeader->e_magic == (u16)IMAGE_DOS_SIGNATURE){
				//printf("\nprobable dos header at: 0x%08X, e_lfanew=0x%08X", i_addr, dosHeader->e_lfanew);
	
				if((u32)dosHeader->e_lfanew < (u32)SCANMZPE_MAXPEHEADEROFFSET){			
					ntHeader_paddr = windows_getphysicaladdress(vcpu, i_addr + (u32)dosHeader->e_lfanew);
					
					if(ntHeader_paddr > 0x00100000 && ntHeader_paddr < LDN_ENV_PHYSICALMEMORYLIMIT){
						ntHeader= (IMAGE_NT_HEADERS32 *)ntHeader_paddr;
						
						//sanity check: check if complete NT Headers is within the physical page
						//if( (u32)dosHeader->e_lfanew + sizeof(IMAGE_NT_HEADERS32) > 4096)
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



#if 0
//------------------------------------------------------------------------------
//sanity checks PE image in memory and obtains relocation information into
//provided buffer
//input: relocinfobuffer __must__ be of size MAX_RELOCATIONINFOSIZE
//returns: UNRELOC_SUCCESS on success, else one of UNRELOC_ERR_xxx on error
u32 windows_checkPEandgetrelocsection(IMAGE_NT_HEADERS32 *ntHeader,
	u32 imagebase, u8 *relocinfobuffer){
	u32 originalimagebase;
	u32 reloc_size, reloc_vaddr;
	u32 retval;
	
	//get PE original image base from header
	originalimagebase=ntHeader->OptionalHeader.ImageBase;
  	
	//PE should never be relocated to an address "below" its imagebase
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
	memset(relocinfobuffer, 0, MAX_RELOCATIONINFOSIZE);
	retval=windows_getrelocsection(imagebase+reloc_vaddr, reloc_size, relocinfobuffer);
	if(retval != UNRELOC_SUCCESS){
		AX_DEBUG(("\n error: unable to get relocation info!"));
		return retval;
	}
	
	return UNRELOC_SUCCESS;
}
#endif


#if 1
//==============================================================================
//PE relocation routines
typedef struct {
	u32 offset : 12;
	u32 type : 4;
} RELOCTYPEOFFSET;

#define MAX_RELOCATIONINFOSIZE	(0x20000)
u8 relocationInfo[MAX_RELOCATIONINFOSIZE];


#define	UNRELOC_SUCCESS_UNRELOCATED						0x0
#define UNRELOC_SUCCESS_NOUNRELOCATIONNEEDED	0x1
#define	UNRELOC_SUCCESS												0x2
#define UNRELOC_ERR_UNHANDLEDTYPE							0x3
#define UNRELOC_ERR_SECTIONNOTINMEM						0x4
#define	UNRELOC_ERR_SECTIONNOTONPAGEBOUNDARY	0x5
#define	UNRELOC_ERR_IMAGEBASE									0x6
#define	UNRELOC_ERR_BUFEXCEEDED								0x7
#define UNRELOC_ERR_ZEROBLOCK									0x8
#define	UNRELOC_ERR_NOPHYSMEM									0x9

u32 windows_getrelocsection(VCPU *vcpu, u32 reloc_section_va, u32 reloc_section_size, u8 *relocBuffer){
	u32 paligned_reloc_section_va;
	u32 paligned_reloc_section_va_end;
	u32 vaddr, paddr;
	u32 offset=0;
	
	AX_DEBUG(("\n  windows_getrelocsection:"));
	AX_DEBUG(("\n  reloc_section_va=0x%08x, size=0x%08x, relocBuffer=0x%08x", 
		reloc_section_va, reloc_section_size, (u32)relocBuffer));
		
	paligned_reloc_section_va = PAGE_ALIGN_4K(reloc_section_va); 	//page align reloc_section_va
	paligned_reloc_section_va_end = paligned_reloc_section_va + PAGE_ALIGN_4K(reloc_section_size);
	AX_DEBUG(("\n  paligned_reloc_section_va=0x%08x, paligned_reloc_section_va_end=0x%08x", paligned_reloc_section_va,
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
			memcpy((void *)((u32)relocBuffer+offset), (void *)paddr, (reloc_section_size % PAGE_SIZE_4K));
		else
			memcpy((void *)((u32)relocBuffer+offset), (void *)paddr, PAGE_SIZE_4K);

		offset+=PAGE_SIZE_4K;		
	}

	
	return UNRELOC_SUCCESS;
}

u8 unrelocateBuffer[PAGE_SIZE_4K * 3];


u32 windows_unrelocatepage_processrelocations(VCPU *vcpu, u32 imagebase, u32 originalimagebase,
	void *page, IMAGE_BASE_RELOCATION *relocEntry, u8 *relocEntry_relocInfo){
	
	u32 i;
	RELOCTYPEOFFSET *relocTypeOffsets;
	u32 relocvalue, *relocaddr;
	
	(void)vcpu;
	
	for(i=0; i < ((relocEntry->SizeOfBlock-8)/sizeof(unsigned short int)); i++){
		relocTypeOffsets = (RELOCTYPEOFFSET *)( (u8 *)relocEntry_relocInfo + (i*2));
		//if(vaddr == 0x8084d426)
		//	AX_DEBUG(("\nEntry %u: Type=%x, Offset=%x", i, relocTypeOffsets->type, relocTypeOffsets->offset));
		
		if(relocTypeOffsets->type == 3){
			relocvalue=	imagebase-originalimagebase;
			relocaddr = (u32 *)( (ULONG)page + relocTypeOffsets->offset);
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
//u32 windows_unrelocatepage(IMAGE_NT_HEADERS32 *ntHeader, u32 imagebase, u32 vaddr, void *inputPage, void *outputPage){
u32 windows_unrelocatepage(VCPU *vcpu, IMAGE_NT_HEADERS32 *ntHeader, u32 imagebase, u32 vaddr, void *inputPagePrevious, void *inputPage, void *inputPageNext, void *outputPage){
	IMAGE_BASE_RELOCATION *relocEntry;
	IMAGE_BASE_RELOCATION	*relocEntryPrevious=NULL;
	IMAGE_BASE_RELOCATION *relocEntryNext=NULL;
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

#if 0	
	u32 i;
	RELOCTYPEOFFSET *relocTypeOffsets;
	u32 needPreviousPage=0, needNextPage=0;
#else
	(void)outputPage;
#endif
	
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
	relocEntry = (IMAGE_BASE_RELOCATION *)relocationInfo;
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
				relocEntryNext = (IMAGE_BASE_RELOCATION *)( (u8 *)relocationInfo + current_size);
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
		relocEntry = (IMAGE_BASE_RELOCATION *)( (u8 *)relocationInfo + current_size);
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
		
#if 0
	memset(&unrelocateBuffer, 0, (PAGE_SIZE_4K *3));

	//determine if we need the previous page to perform a successful unrelocation
	if(relocEntryPrevious){
		for(i=0; i < ((relocEntryPrevious->SizeOfBlock-8)/sizeof(unsigned short int)); i++){
			relocTypeOffsets = (RELOCTYPEOFFSET *)( (u8 *)relocEntryPrevious_relocInfo + (i*2));
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
			relocTypeOffsets = (RELOCTYPEOFFSET *)( (u8 *)relocEntryNext_relocInfo + (i*2));
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
#endif
	
	return UNRELOC_SUCCESS_UNRELOCATED;
}
// end PE relocation code
//==============================================================================
#endif



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
	IMAGE_NT_HEADERS32 *ntHeader;
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
	vaddr = windows_getvirtualaddress(vcpu, paddr);
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

		if(!retval){
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
		}
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

