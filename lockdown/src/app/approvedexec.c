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

// approved execution implementation for lockdown
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>

#include <lockdown.h>


u32 ax_debug_flag = 0;


//the trusted environment hash-lists
struct hashinfo hashlist_full[MAX_FULL_HASHLIST_ELEMENTS];
u32 hashlist_full_totalelements = 0;

struct hashinfo hashlist_partial[MAX_PARTIAL_HASHLIST_ELEMENTS];
u32 hashlist_partial_totalelements=0;


//----------------------------------------------------------------------
// setup approved execution
//----------------------------------------------------------------------
void approvedexec_setup(VCPU *vcpu, APP_PARAM_BLOCK *apb){
	LDNPB *pldnPb = (LDNPB *) apb->optionalmodule_ptr;
    u32 endpfn = (apb->runtimephysmembase-PAGE_SIZE_2M) / PAGE_SIZE_4K;
    u32 i;
	u8 *addr_hashlist_full, *addr_hashlist_partial;
	
	printf("\nCPU(0x%02x): %s: starting...", 
		vcpu->id, __FUNCTION__);

	//populate full and partial hash lists using the TE parameter
	//block, sanity check along the way
	
		//grab total elements for full and partial hash lists
		hashlist_full_totalelements = pldnPb->full_hashlist_count;
		hashlist_partial_totalelements = pldnPb->partial_hashlist_count;
	
		printf("\nCPU(0x%02x): %s: populating hash lists (full=%u, \
			partial=%u elements)", vcpu->id, __FUNCTION__,
			hashlist_full_totalelements, hashlist_partial_totalelements);
	
		//sanity check
		if( (hashlist_full_totalelements > MAX_FULL_HASHLIST_ELEMENTS) ||
			(hashlist_partial_totalelements > MAX_PARTIAL_HASHLIST_ELEMENTS) ){
			printf("\nCPU(0x%02x): %s: total no. of hash list elements \
				exceeds max. supported value. Halting!", vcpu->id,
				__FUNCTION__);
			HALT();
		}
	
		//zero initialize hashlist_full and hashlist_partial arrays
		memset( (void *)&hashlist_full, 0, (sizeof(struct hashinfo) * MAX_FULL_HASHLIST_ELEMENTS) );
		memset( (void *)&hashlist_partial, 0, (sizeof(struct hashinfo) * MAX_PARTIAL_HASHLIST_ELEMENTS) );
	
		//compute address of full and partial struct hashinfo lists
		//within the TE parameter block
		addr_hashlist_full = (u8 *)((u32)&pldnPb->partial_hashlist_count + sizeof(u32));
		addr_hashlist_partial = (u8 *)( ((u32)&pldnPb->partial_hashlist_count + sizeof(u32)) + 
				(hashlist_full_totalelements * sizeof(struct hashinfo)) );
	
		//copy the full and partial struct hashinfo lists to our
		//arrays
		memcpy( (void *)&hashlist_full, (void *)addr_hashlist_full, (hashlist_full_totalelements * sizeof(struct hashinfo)) );
		memcpy( (void *)&hashlist_partial, (void *)addr_hashlist_partial, (hashlist_partial_totalelements * sizeof(struct hashinfo)) );
	
	  /*//[DEBUG]
	  {
		u32 i, j;
		printf("\nCPU(0x%02x): %s: full hash list dump follows...",
			vcpu->id, __FUNCTION__);
		for(i=(hashlist_full_totalelements-1); i > (hashlist_full_totalelements-16); i--){
			printf("\n%08x:%08x:", hashlist_full[i].pageoffset, 
							hashlist_full[i].size);
			for(j=0; j < 20; j++)
				printf("%02x", hashlist_full[i].shanum[j]);
		}
		printf("\nCPU(0x%02x): %s: partial hash list dump follows...",
			vcpu->id, __FUNCTION__);
		for(i=(hashlist_partial_totalelements-1); i > (hashlist_partial_totalelements-16); i--){
			printf("\n%08x:%08x:", hashlist_partial[i].pageoffset, 
							hashlist_partial[i].size);
			for(j=0; j < 20; j++)
				printf("%02x", hashlist_partial[i].shanum[j]);
		}
		HALT();
	  }*/
		
      //start with all guest physical memory pages as non-executable
      printf("\nCPU(0x%02x): %s: setting guest physical memory \
		0x%08x-0x%08x (%u pfns) as NX",
		vcpu->id, 0, (apb->runtimephysmembase-PAGE_SIZE_2M), endpfn);
		
      for(i=0x0; i < endpfn; i++){
		//note: we really only support approved execution for 32-bit
		//protected mode guest code, so we skip the first 1MB of guest
		//physical memory where 16-bit boot-strap code executes
		//we also skip the nt kernel physical memory region as 
		//the hibernation resume code does not seem to like NX
		//trapping (causes a restart) 
		if(i < 0x100 || (i >=0x800 && i <= 0x1000) )
			continue;

        emhf_memprot_setprot(vcpu, (i*PAGE_SIZE_4K), 
					(MEMP_PROT_PRESENT | 
						MEMP_PROT_READWRITE | MEMP_PROT_NOEXECUTE) );     
	  }
	
      emhf_memprot_flushmappings(vcpu);  //flush all NPT/EPT mappings
      printf("\nCPU(0x%02x): %s: setup approved execution.", 
			vcpu->id, __FUNCTION__);

}

//checks the sha-1 hash of the provided 4K memory page with physical address
//pagebase_paddr (assumed to be page-aligned). 
//return: 1 if there is a matching hash for this page else 0
u32 approvedexec_checkhashes(u32 pagebase_paddr, u32 *index, u32 *fullhash){
  u8 sha1sum[SHA_DIGEST_LENGTH];

	u32 i;

	//start by computing a sha-1 on the complete page
  sha1_buffer((const u8 *)pagebase_paddr, PAGE_SIZE_4K, sha1sum);


	//printf("\nSHA-1 = ");
	//for(i=0; i < 20; i++){
	//	putstr(_ultoa((unsigned long)sha1sum[i], &buf, 16)); putstr(" ");
	//}
	
	//first scan the full hashlist to find a match
	for(i=0; i <hashlist_full_totalelements; i++){
		if (memcmp(hashlist_full[i].shanum, sha1sum, SHA_DIGEST_LENGTH) == 0){
     	*index = i;
     	*fullhash = 1;     	
			 //AX_DEBUG(("\nSUCCESS(Full Hash List) for %s", hashlist_full[i].name));
		  return 1;
    }
	}

#if 1
	//now scan the partial hashlist computing checksum for each 
	for(i=0; i <hashlist_partial_totalelements;i++){
		sha1_buffer((const u8 *)hashlist_partial[i].pageoffset+pagebase_paddr, hashlist_partial[i].size,
                sha1sum);

		if (memcmp(hashlist_partial[i].shanum, sha1sum, SHA_DIGEST_LENGTH) == 0){
     	 *index = i;
     	 *fullhash=0;     	 
			 //AX_DEBUG(("\nSUCCESS(Part Hash List) for %s", hashlist_partial[i].name));
		  return 1;
    }
	}
#endif

	return 0;	
}



//---returns virtual address of current guest program counter-----------
static u32 approvedexec_getguestpcvaddr(VCPU *vcpu){
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		struct _svm_vmcbfields *vmcb;
		vmcb = (struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr;
		return ((u32)vmcb->cs.base + (u32)vmcb->rip);
	}else{	//CPU_VENDOR_INTEL
		return (u32)vcpu->vmcs.guest_CS_base + (u32)vcpu->vmcs.guest_RIP; 		
	}
}

//---returns physical address of current guest program counter----------
static u32 approvedexec_getguestpcpaddr(VCPU *vcpu){
	u32 guestpclinearaddress=0;
	u32 guest_cr0=0;

	//get linear address of guest PC
	guestpclinearaddress = approvedexec_getguestpcvaddr(vcpu);

	//get guest CR0 value
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD)
		guest_cr0 = (u32)((struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr)->cr0;
	else // CPU_VENDOR_INTEL
		guest_cr0 = (u32) vcpu->vmcs.guest_CR0;

	//if we have paging turned on, then go through the guest page tables
	if( (guest_cr0 & CR0_PE) && (guest_cr0 & CR0_PG) ){
		u32 guestpcpaddr = (u32)(u32 *)emhf_smpguest_walk_pagetables(vcpu, guestpclinearaddress);
		ASSERT(guestpcpaddr != 0xFFFFFFFFUL);
		return (u32)guestpcpaddr;  
	}else{ //linear address is physical address when no paging in effect
		return (u32)guestpclinearaddress; 
	}
}

//---returns 1 if code-modifying-data (cmd) falls on the same physical 
//memory page, else 0
u32 approvedexec_iscmdonsamepage(VCPU *vcpu, u64 gpa, u64 gva){
  u32 pagealigned_pc, pagealigned_gpa;
  (void)gva;
  
  //obtain page-aligned program counter physical address
  pagealigned_pc = PAGE_ALIGN_4K(approvedexec_getguestpcpaddr(vcpu));

  //now check if this is equal to the page-aligned gpa for violation
  //if so we have cmd on same page
  pagealigned_gpa = PAGE_ALIGN_4K(gpa);
  
  if(pagealigned_pc == pagealigned_gpa)
    return 1; //cmd on same page
  else
    return 0; //not cmd on same page
}
                
//---return true if a page table fault was due to execute---------------
bool ispfduetoexec(VCPU *vcpu, u64 violationcode){
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		if ( ((u32)violationcode & VMCB_NPT_ERRORCODE_P ) &&
			 ((u32)violationcode & VMCB_NPT_ERRORCODE_ID) )
			 return true;
	}else{ //CPU_VENDOR_INTEL
		if ( ((u32)violationcode & EPT_ERRORCODE_EXEC ) )
			 return true;
	}

	return false;
}                
                  
//---approved execution violation handler-------------------------------                                                                   
u32 approvedexec_handleevent(VCPU *vcpu, struct regs *r, 
  u64 gpa, u64 gva, u64 violationcode){
  (void)r;

  //printf("\n%s: CPU(0x%02x) PF, p=0x%08x, v=0x%08x, pcp=0x%08x, pcv=0x%08x",
	//__FUNCTION__, vcpu->id, (u32)gpa, (u32)gva, 
	//approvedexec_getguestpcpaddr(vcpu), 
	//approvedexec_getguestpcvaddr(vcpu));

  
  if(ispfduetoexec(vcpu, violationcode)){
    //we had a exec violation, time to check this physical page and lock it
    //printf("\n%s: CPU(0x%02x) PF-NX, p=0x%08x, v=0x%08x, pcp=0x%08x, pcv=0x%08x",
	//	__FUNCTION__, vcpu->id, (u32)gpa, (u32)gva, 
	//	approvedexec_getguestpcpaddr(vcpu), 
	//	approvedexec_getguestpcvaddr(vcpu));

    //verify integrity of code page
    windows_verifycodeintegrity(vcpu, (u32)gpa, (u32)gva);
    //give page execute permissions but prevent further writes
    emhf_memprot_setprot(vcpu, gpa, MEMP_PROT_PRESENT | MEMP_PROT_READONLY | MEMP_PROT_EXECUTE);
    //emhf_memprot_setprot(vcpu, gpa, MEMP_PROT_PRESENT | MEMP_PROT_READWRITE | MEMP_PROT_EXECUTE);
    //printf("\n%s: CPU(0x%02x) PF-NX, getprot=0x%08x",
	//	__FUNCTION__, vcpu->id, emhf_memprot_getprot(vcpu, gpa));

  }else{
    //we have a write fault, check if it is cmd on same page
    //printf("\n%s: CPU(0x%02x) PF-W, p=0x%08x, v=0x%08x, pcp=0x%08x, pcv=0x%08x",
	//	__FUNCTION__, vcpu->id, (u32)gpa, (u32)gva, 
	//	approvedexec_getguestpcpaddr(vcpu), 
	//	approvedexec_getguestpcvaddr(vcpu));

    if(approvedexec_iscmdonsamepage(vcpu, gpa, gva)){
      //TODO: we will need to single-step or emulate instructions on this page  
      //for now give all permissions and move on...
      //printf("\n  CPU(0x%02x): C-M-D on same page", vcpu->id);
      emhf_memprot_setprot(vcpu, gpa, MEMP_PROT_PRESENT | MEMP_PROT_READWRITE | MEMP_PROT_EXECUTE);
    }else{
      //make page read-write and remove execute permission
      emhf_memprot_setprot(vcpu, gpa, MEMP_PROT_PRESENT | MEMP_PROT_READWRITE | MEMP_PROT_NOEXECUTE);
    }
  }

  emhf_memprot_flushmappings(vcpu);  //flush all NPT/EPT mappings

  return APP_SUCCESS;    
}

