// approved execution implementation for lockdown
// author: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h>

#include <lockdown.h>

#include <approvedexec.h>
#include <exe_pe.h>
//#include <sha1.h>

u32 ax_debug_flag = 0;


//the trusted environment hash-lists
struct hashinfo hashlist_full[] = {
//#include "hashlist_full.dat"
};
u32 hashlist_full_totalelements= (sizeof(hashlist_full)/sizeof(struct hashinfo));

struct hashinfo hashlist_partial[] = {
//#include "hashlist_partial.dat"
};
u32 hashlist_partial_totalelements= (sizeof(hashlist_partial)/sizeof(struct hashinfo));

//checks the sha-1 hash of the provided 4K memory page with physical address
//pagebase_paddr (assumed to be page-aligned). 
//return: 1 if there is a matching hash for this page else 0
u32 approvedexec_checkhashes(u32 pagebase_paddr, u32 *index, u32 *fullhash){
	sha1_context ctx;
  unsigned char sha1sum[SHA1_CHECKSUM_LEN];
	u32 i;

	//start by computing a sha-1 on the complete page
  sha1_starts(&ctx);
  sha1_update(&ctx, (const unsigned char *)pagebase_paddr, PAGE_SIZE_4K);
  sha1_finish(&ctx, sha1sum);

	//printf("\nSHA-1 = ");
	//for(i=0; i < 20; i++){
	//	putstr(_ultoa((unsigned long)sha1sum[i], &buf, 16)); putstr(" ");
	//}
	
	//first scan the full hashlist to find a match
	for(i=0; i <hashlist_full_totalelements; i++){
		if (memcmp(hashlist_full[i].shanum, sha1sum, SHA1_CHECKSUM_LEN) == 0){
     	*index = i;
     	*fullhash = 1;     	
			 AX_DEBUG(("\nSUCCESS(Full Hash List) for %s", hashlist_full[i].name));
		  return 1;
    }
	}

#if 1
	//now scan the partial hashlist computing checksum for each 
	for(i=0; i <hashlist_partial_totalelements;i++){
	  sha1_starts(&ctx);
  	sha1_update(&ctx, (const unsigned char *)hashlist_partial[i].pageoffset+pagebase_paddr, hashlist_partial[i].size);
  	sha1_finish(&ctx, sha1sum);

		if (memcmp(hashlist_partial[i].shanum, sha1sum, SHA1_CHECKSUM_LEN) == 0){
     	 *index = i;
     	 *fullhash=0;     	 
			 AX_DEBUG(("\nSUCCESS(Part Hash List) for %s", hashlist_partial[i].name));
		  return 1;
    }
	}
#endif

	return 0;	
}



//---returns virtual address of current guest program counter-------------------
static u32 approvedexec_getguestpcvaddr(VCPU *vcpu){
  return (u32)vcpu->vmcs.guest_CS_base + (u32)vcpu->vmcs.guest_RIP; 
}

//---returns physical address of current guest program counter------------------
static u32 approvedexec_getguestpcpaddr(VCPU *vcpu){
  u32 guestpclinearaddress=0;

  //get linear address of guest PC
  guestpclinearaddress = approvedexec_getguestpcvaddr(vcpu);

//if(vcpu->guest_unrestricted){
	//if paging is enabled, then we walk the guest page-table to obtain
  //the physical address
  if( (vcpu->vmcs.guest_CR0 & CR0_PE) &&
    (vcpu->vmcs.guest_CR0 & CR0_PG) ){
    u32 guestpcpaddr = emhf_smpguest_walk_pagetables(vcpu, guestpclinearaddress);
    ASSERT(guestpcpaddr != 0xFFFFFFFFUL);
    return (u32)guestpcpaddr;  
  }else{
    return (u32)guestpclinearaddress; //linear address is physical address when no paging in effect
  }
//}
/*else{
	//if paging is enabled, then we walk the guest page-table to obtain
  //the physical address
  if( (vcpu->guest_currentstate & GSTATE_PROTECTEDMODE) &&
    (vcpu->guest_currentstate & GSTATE_PROTECTEDMODE_PG) ){
    u32 guestpcpaddr = emhf_guestpgtbl_walk(vcpu, guestpclinearaddress);
    ASSERT(guestpcpaddr != 0xFFFFFFFFUL);
    return (u32)guestpcpaddr;  
  }else{
    return (u32)guestpclinearaddress; //linear address is physical address when no paging in effect
  }
}*/  
  
}

//---returns 1 if code-modifying-data (cmd) falls on the same physical---------- 
//memory page, else 0
u32 approvedexec_iscmdonsamepage(VCPU *vcpu, u64 gpa, u64 gva){
  u32 pagealigned_pc, pagealigned_gpa;
  
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
                  
//---approved execution violation handler---------------------------------------                                                                   
u32 approvedexec_handleevent(VCPU *vcpu, struct regs *r, 
  u64 gpa, u64 gva, u64 violationcode){
  
  if(violationcode & HWPGTBL_FLAG_EXECUTE){
    //printf("\nCPU(0x%02x): EPT/EXEC, p=0x%08x, v=0x%08x, pcp=0x%08x, pcv=0x%08x",
    // vcpu->id, (u32)gpa, (u32)gva, approvedexec_getguestpcpaddr(vcpu), approvedexec_getguestpcvaddr(vcpu));
    //we had a exec violation, time to check this physical page and lock it
    //TODO: check hash
    windows_verifycodeintegrity(vcpu, (u32)gpa, (u32)gva);
    //give page execute permissions but prevent further writes
    emhf_hwpgtbl_setprot(vcpu, gpa, HWPGTBL_FLAG_READ | HWPGTBL_FLAG_EXECUTE);

  }else{
    //printf("\nCPU(0x%02x): EPT/WR, p=0x%08x, v=0x%08x, pcp=0x%08x, pcv=0x%08x",
    //  vcpu->id, (u32)gpa, (u32)gva, approvedexec_getguestpcpaddr(vcpu), approvedexec_getguestpcvaddr(vcpu));
    //we have a write fault, check if it is cmd on same page
    if(approvedexec_iscmdonsamepage(vcpu, gpa, gva)){
      //TODO: we will need to single-step or emulate instructions on this
      //page  
      //printf("\n  CPU(0x%02x): C-M-D on same page", vcpu->id);
      //for now give all permissions
      emhf_hwpgtbl_setprot(vcpu, gpa, 
           HWPGTBL_FLAG_READ | HWPGTBL_FLAG_WRITE | HWPGTBL_FLAG_EXECUTE);
    }else{
      //make page read-write and remove execute permission
      emhf_hwpgtbl_setprot(vcpu, gpa, HWPGTBL_FLAG_READ | HWPGTBL_FLAG_WRITE);
    }
  }

  return APP_SUCCESS;    
}

