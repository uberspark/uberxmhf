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

// islayer_svm.c - SVM isolation layer implementation
// author: amit vasudevan (amitvasudevan@acm.org) and ning qu (qning@cmu.edu)
// modified extensively for EMHF by amit vasudevan
#include <emhf.h> 

//---notes
// CLGI/STGI
// GIF is set to 1 always when reset and SVM first enabled
// if you send an NMI when GIF=0, it is held pending until GIF=1 again

// so we set GIF=1 on all cores and NMI intercept as well
// when we get the VMEXIT_NMI, we do a simple trick
// CLGI followed by STGI this will make GIF=0 and then GIF=1 which will
// deliver the pending NMI to the current IDT whichi will xfer control
// to the exception handler within the hypervisor where we quiesce.
// upon resuming the hypervisor or guest resumes normally!


//u8 * _svm_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);






//==============================================================================
//SVM EMHF library interface implementation

/*
//---IOPM Bitmap interface------------------------------------------------------
static void _svm_lib_iopm_set_write(VCPU __attribute__((unused)) *vcpu, u32 __attribute__((unused)) port, u32 __attribute__((unused)) size){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}

//---MSRPM Bitmap interface------------------------------------------------------
static void _svm_lib_msrpm_set_write(VCPU __attribute__((unused)) *vcpu, u32 __attribute__((unused)) msr){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}*/

/*//---hardware pagetable flush-all routine---------------------------------------
static void _svm_lib_hwpgtbl_flushall(VCPU *vcpu){
	((struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr))->tlb_control=TLB_CONTROL_FLUSHALL;
}*/

/*//---hardware pagetable protection manipulation routine-------------------------
static void _svm_lib_hwpgtbl_setprot(VCPU __attribute__((unused)) *vcpu, u64 __attribute__((unused)) gpa, u64 __attribute__((unused)) flags){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}

static void __attribute__((unused)) _svm_lib_hwpgtbl_setentry(VCPU __attribute__((unused)) *vcpu, u64 __attribute__((unused)) gpa, u64 __attribute__((unused)) value){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}*/

/*static u64 _svm_lib_hwpgtbl_getprot(VCPU __attribute__((unused)) *vcpu, u64 __attribute__((unused)) gpa){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT(); return 0; // dummy return; appeases compiler 
}*/

/*//---guest page-table walker, returns guest physical address--------------------
//note: returns 0xFFFFFFFF if there is no mapping
u8 * _svm_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr){
	struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;

  if((u32)vmcb->cr4 & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)vmcb->cr3;
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
    u32 kcr3 = (u32)vmcb->cr3;
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


//---reboot functionality-------------------------------------------------------
/*static void _svm_lib_reboot(VCPU __attribute__((unused)) *vcpu){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}*/


struct emhf_library g_emhf_library_svm = {
	//.emhf_iopm_set_write = _svm_lib_iopm_set_write,
	//.emhf_msrpm_set_write = _svm_lib_msrpm_set_write,
	//.emhf_hwpgtbl_flushall = _svm_lib_hwpgtbl_flushall,
	//.emhf_hwpgtbl_setprot = _svm_lib_hwpgtbl_setprot,
	//.emhf_hwpgtbl_getprot = _svm_lib_hwpgtbl_getprot,
	//.emhf_guestpgtbl_walk = _svm_lib_guestpgtbl_walk,
	//.emhf_reboot = _svm_lib_reboot,
};



