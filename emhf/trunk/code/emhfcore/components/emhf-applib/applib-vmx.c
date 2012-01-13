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
// islayer_vmx.c - VMX isolation layer implementation
// author: amit vasudevan (amitvasudevan@acm.org) 

#include <emhf.h> 

//==============================================================================
// static (local) data
//==============================================================================



//==============================================================================
// static (local) function definitions
//==============================================================================
//u8 *_vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);











//==============================================================================
//VMX EMHF library interface implementation
static void _vmx_set_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] |= (1 << bit_offset);

  return;                        
}

static void __attribute__((unused)) _vmx_clear_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] &= ~(1 << bit_offset);

  return;
}

static u32 __attribute__((unused)) _vmx_test_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  if (bit_vector[byte_offset] & (1 << bit_offset))
    return 1;
  else 
    return 0;
}

/*
//---IOPM Bitmap interface------------------------------------------------------
static void _vmx_lib_iopm_set_write(VCPU *vcpu, u32 port, u32 size){
  u32 i;
  for (i = 0; i < size; i ++)
    _vmx_set_page_prot((port+i), (u8 *)vcpu->vmx_vaddr_iobitmap);
}

//---MSRPM Bitmap interface------------------------------------------------------
static void _vmx_lib_msrpm_set_write(VCPU __attribute__((unused)) *vcpu, u32 __attribute__((unused)) msr){
  return;
}*/

/*//---hardware pagetable flush-all routine---------------------------------------
static void _vmx_lib_hwpgtbl_flushall(VCPU *vcpu){
  __vmx_invept(VMX_EPT_SINGLE_CONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full, 
          0);
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}*/

/*//---hardware pagetable protection manipulation routine-------------------------
static void _vmx_lib_hwpgtbl_setprot(VCPU *vcpu, u64 gpa, u64 flags){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;

  pt[pfn] &= ~(u64)7; //clear all previous flags
  pt[pfn] |= flags; //set new flags

	//flush TLB
	//_vmx_lib_hwpgtbl_flushall(vcpu);
}*/

/*static void __attribute__((unused)) _vmx_lib_hwpgtbl_setentry(VCPU *vcpu, u64 gpa, u64 value){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;

  pt[pfn] = value; //set new value

  //flush the EPT mappings for changes to take effect
//	_vmx_lib_hwpgtbl_flushall(vcpu);
}*/

/*static u64 _vmx_lib_hwpgtbl_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;

  return (pt[pfn] & (u64)7) ;
}*/

/*
//---guest page-table walker, returns guest physical address--------------------
//note: returns 0xFFFFFFFF if there is no mapping
u8 * _vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr){

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
  
    return (u8 *)(u32)paddr;
    
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
  
    return (u8 *)(u32)paddr;
  }
}*/

/*
//---reboot functionality-------------------------------------------------------
static void _vmx_lib_reboot(VCPU __attribute__((unused)) *vcpu){

    printf("\nHello from _vmx_lib_reboot\n");
    if(txt_is_launched()) {
        printf("\nI detect that we are in a TXT environment.  Doing special TXT reboot\n");
    }

	//step-1: shut VMX off, else CPU ignores INIT signal!
	__asm__ __volatile__("vmxoff \r\n");
	write_cr4(read_cr4() & ~(CR4_VMXE));
	
	//step-2: zero out IDT
	emhf_xcphandler_resetIDT();
	
	//step-3: execute ud2 instruction to generate triple fault
	__asm__ __volatile__("ud2 \r\n");
	
	//never get here
	printf("\n%s: should never get here. halt!", __FUNCTION__);
	HALT();
}*/

/*
struct emhf_library g_emhf_library_vmx = {
	//.emhf_iopm_set_write = _vmx_lib_iopm_set_write,
	//.emhf_msrpm_set_write = _vmx_lib_msrpm_set_write,
	//.emhf_hwpgtbl_flushall = _vmx_lib_hwpgtbl_flushall,
	//.emhf_hwpgtbl_setprot = _vmx_lib_hwpgtbl_setprot,
	//.emhf_hwpgtbl_getprot = _vmx_lib_hwpgtbl_getprot,
	//.emhf_guestpgtbl_walk = _vmx_lib_guestpgtbl_walk,
	//.emhf_reboot = _vmx_lib_reboot,
};*/



