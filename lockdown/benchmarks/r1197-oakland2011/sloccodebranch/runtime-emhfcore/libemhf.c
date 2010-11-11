//libemhf - emhf library routines for applications
//author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <target.h>
#include <libemhf.h>


//---globals referenced by this module------------------------------------------
// none


static void __set_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] |= (1 << bit_offset);

  return;                        
}

static void __clear_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] &= ~(1 << bit_offset);

  return;
}

static u32 __test_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  if (bit_vector[byte_offset] & (1 << bit_offset))
    return 1;
  else 
    return 0;
}



//---IOPM Bitmap interface------------------------------------------------------
void emhf_iopm_set_write(VCPU *vcpu, u32 port, u32 size){
  u32 i;

  for (i = 0; i < size; i ++)
    __set_page_prot((port+i), (u8 *)vcpu->vmx_vaddr_iobitmap);
}

//---MSRPM Bitmap interface------------------------------------------------------
void emhf_msrpm_set_write(VCPU *vcpu, u32 msr){
  return;
}

//---reboot functionality-------------------------------------------------------
void emhf_reboot(void){
	//step-1: shut VMX off, else CPU ignores INIT signal!
	__asm__ __volatile__("vmxoff \r\n");
	write_cr4(read_cr4() & ~(CR4_VMXE));
	
	//step-2: zero out IDT
	{
		extern u32 x_idt_start[];
		memset((void *)x_idt_start, 0, PAGE_SIZE_4K);
	}
	
	//step-3: execute ud2 instruction to generate triple fault
	__asm__ __volatile__("ud2 \r\n");
	
	//never get here
	printf("\n%s: should never get here. halt!", __FUNCTION__);
	HALT();
}

#if defined(__NESTED_PAGING__)
//---hardware pagetable flush-all routine---------------------------------------
void emhf_hwpgtbl_flushall(VCPU *vcpu){
  __vmx_invept(VMX_EPT_SINGLE_CONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full, 
          0);
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}

//---hardware pagetable protection manipulation routine-------------------------
void emhf_hwpgtbl_setprot(VCPU *vcpu, u64 gpa, u64 flags){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  pt[pfn] &= ~(u64)7; //clear all previous flags
  pt[pfn] |= flags; //set new flags
  //flush the EPT mappings for new protections to take effect
  __vmx_invept(VMX_EPT_SINGLE_CONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full, 
          0);
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}

void emhf_hwpgtbl_setentry(VCPU *vcpu, u64 gpa, u64 value){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  pt[pfn] = value; //set new value
  //flush the EPT mappings for changes to take effect
  __vmx_invept(VMX_EPT_SINGLE_CONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full, 
          0);
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}


u64 emhf_hwpgtbl_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  return (pt[pfn] & (u64)7) ;
}

#endif

//---guest page-table walker, returns guest physical address--------------------
//note: returns 0xFFFFFFFF if there is no mapping
u32 emhf_guestpgtbl_walk(VCPU *vcpu, u32 vaddr){
  if((u32)vcpu->vmcs.guest_CR4 & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)vcpu->vmcs.guest_CR3;
    u32 pdpt_index, pd_index, pt_index, offset;
    u64 paddr;
    pdpt_t kpdpt;
    pdt_t kpd; 
    pt_t kpt; 
    u32 pdpt_entry, pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pdpt_index = pae_get_pdpt_index(vaddr);
    pd_index = pae_get_pdt_index(vaddr);
    pt_index = pae_get_pt_index(vaddr);
    offset = pae_get_offset_4K_page(vaddr);  

    //grab pdpt entry
    tmp = pae_get_addr_from_32bit_cr3(kcr3);
    kpdpt = (pdpt_t)((u32)tmp); 
    pdpt_entry = kpdpt[pdpt_index];
  
    //grab pd entry
    tmp = pae_get_addr_from_pdpe(pdpt_entry);
    kpd = (pdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)pae_get_addr_from_pde(pd_entry);
      kpt = (pt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      // find physical page base addr from page table entry 
      paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 2MB page 
      offset = pae_get_offset_big(vaddr);
      paddr = (u64)pae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u32)paddr;
    
  }else{
    //non-PAE 2 level paging used by guest
    u32 kcr3 = (u32)vcpu->vmcs.guest_CR3;
    u32 pd_index, pt_index, offset;
    u64 paddr;
    npdt_t kpd; 
    npt_t kpt; 
    u32 pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pd_index = npae_get_pdt_index(vaddr);
    pt_index = npae_get_pt_index(vaddr);
    offset = npae_get_offset_4K_page(vaddr);  
  
    // grab pd entry
    tmp = npae_get_addr_from_32bit_cr3(kcr3);
    kpd = (npdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];
  
    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)npae_get_addr_from_pde(pd_entry);
      kpt = (npt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      // find physical page base addr from page table entry 
      paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 4MB page 
      offset = npae_get_offset_big(vaddr);
      paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u32)paddr;
  }
}
