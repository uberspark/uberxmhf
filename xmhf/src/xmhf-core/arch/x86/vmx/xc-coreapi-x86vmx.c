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

// XMHF core API -- x86vmx arch. backend
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf-core.h> 
#include <xc-x86.h>
#include <xc-x86vmx.h>


//----------------------------------------------------------------------
//Queiscing interfaces
//----------------------------------------------------------------------

//the quiesce counter, all CPUs except for the one requesting the
//quiesce will increment this when they get their quiesce signal
static u32 g_vmx_quiesce_counter __attribute__(( section(".data") )) = 0;
static u32 g_vmx_lock_quiesce_counter __attribute__(( section(".data") )) = 1; 

//resume counter to rally all CPUs after resumption from quiesce
static u32 g_vmx_quiesce_resume_counter __attribute__(( section(".data") )) = 0;
static u32 g_vmx_lock_quiesce_resume_counter __attribute__(( section(".data") )) = 1; 
    
//the "quiesce" variable, if 1, then we have a quiesce in process
static u32 g_vmx_quiesce __attribute__(( section(".data") )) = 0;;      
static u32 g_vmx_lock_quiesce __attribute__(( section(".data") )) = 1; 
    
//resume signal, becomes 1 to signal resume after quiescing
static u32 g_vmx_quiesce_resume_signal __attribute__(( section(".data") )) = 0;  
static u32 g_vmx_lock_quiesce_resume_signal __attribute__(( section(".data") )) = 1; 

static void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(xc_cpu_t *xc_cpu, struct regs *r);

static void _vmx_send_quiesce_signal(void){
  u32 prev_icr_high_value;

  prev_icr_high_value = xmhfhw_sysmemaccess_readu32((0xFEE00000 + 0x310));

  xmhfhw_sysmemaccess_writeu32((0xFEE00000 + 0x310), (0xFFUL << 24)); //send to all but self
  xmhfhw_sysmemaccess_writeu32((0xFEE00000 + 0x300), 0x000C0400UL); //send NMI

  while( xmhfhw_sysmemaccess_readu32((0xFEE00000 + 0x310)) & 0x00001000 );
  
  xmhfhw_sysmemaccess_writeu32((0xFEE00000 + 0x310), prev_icr_high_value);
}

//flush EPT TLB
static void _vmx_ept_flushmappings(void){
  __vmx_invept(VMX_INVEPT_SINGLECONTEXT, 
          (u64)xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EPT_POINTER_FULL));
}


//quiesce interface to switch all guest cores into hypervisor mode
//note: we are in atomic processsing mode for this "xc_cpu"
static void _cpu_arch_x86vmx_quiesce(context_desc_t context_desc){
        spin_lock(&g_vmx_lock_quiesce);	        		//grab hold of quiesce lock
		g_xc_cpu[context_desc.cpu_desc.cpu_index].is_quiesced = true;
        spin_lock(&g_vmx_lock_quiesce_counter);
        g_vmx_quiesce_counter=0;						//reset quiesce counter
        spin_unlock(&g_vmx_lock_quiesce_counter);
        g_vmx_quiesce=1;  								//we are now processing quiesce
        _vmx_send_quiesce_signal();				        //send all the other CPUs the quiesce signal
        while(g_vmx_quiesce_counter < (g_xc_primary_partition[context_desc.partition_desc.partition_index].numcpus-1) );         //wait for all the remaining CPUs to quiesce
}

static void _cpu_arch_x86vmx_endquiesce(context_desc_t context_desc){

        g_vmx_quiesce_resume_counter=0;		        //set resume signal to resume the cores that are quiesced
        g_vmx_quiesce_resume_signal=1;
        while(g_vmx_quiesce_resume_counter < (g_xc_primary_partition[context_desc.partition_desc.partition_index].numcpus-1) );	//wait for all cores to resume
		g_xc_cpu[context_desc.cpu_desc.cpu_index].is_quiesced = false;
        g_vmx_quiesce=0;  							// we are out of quiesce at this point
        spin_lock(&g_vmx_lock_quiesce_resume_signal);
        g_vmx_quiesce_resume_signal=0;				        //reset resume signal
        spin_unlock(&g_vmx_lock_quiesce_resume_signal);
        spin_unlock(&g_vmx_lock_quiesce);         //release quiesce lock
}

//quiescing handler for #NMI (non-maskable interrupt) exception event
void xmhf_smpguest_arch_eventhandler_nmiexception(struct regs *r){
	xc_cpu_t *xc_cpu;
	context_desc_t context_desc;
	
	//xc_cpu= _vmx_getxc_cpu();
	context_desc = xc_api_partition_getcontextdesc(xmhf_baseplatform_arch_x86_getcpulapicid());
	if(context_desc.cpu_desc.cpu_index == XC_PARTITION_INDEX_INVALID || context_desc.partition_desc.partition_index == XC_PARTITION_INDEX_INVALID){
		printf("\n%s: invalid partition/cpu context. Halting!\n", __FUNCTION__);
		HALT();
	}
	xc_cpu = &g_xc_cpu[context_desc.cpu_desc.cpu_index];

	xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(xc_cpu, r);
}	

//quiescing handler for #NMI (non-maskable interrupt) exception event
//note: we are in atomic processsing mode for this "xc_cpu"
static void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(xc_cpu_t *xc_cpu, struct regs *r){
	u32 nmiinhvm;	//1 if NMI originated from the HVM else 0 if within the hypervisor
	u32 _vmx_vmcs_info_vmexit_interrupt_information;
	u32 _vmx_vmcs_info_vmexit_reason;

	//determine if the NMI originated within the HVM or within the
	//hypervisor. we use VMCS fields for this purpose. note that we
	//use vmread directly instead of relying on xc_cpu-> to avoid 
	//race conditions
	_vmx_vmcs_info_vmexit_interrupt_information = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION);
	_vmx_vmcs_info_vmexit_reason = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_REASON);
	
	nmiinhvm = ( (_vmx_vmcs_info_vmexit_reason == VMX_VMEXIT_EXCEPTION) && ((_vmx_vmcs_info_vmexit_interrupt_information & INTR_INFO_VECTOR_MASK) == 2) ) ? 1 : 0;
	
	if(g_vmx_quiesce){ //if g_vmx_quiesce =1 process quiesce regardless of where NMI originated from
		//if this core has been quiesced, simply return
			if(xc_cpu->is_quiesced)
				return;
				
			xc_cpu->is_quiesced=1;
	
			//increment quiesce counter
			spin_lock(&g_vmx_lock_quiesce_counter);
			g_vmx_quiesce_counter++;
			spin_unlock(&g_vmx_lock_quiesce_counter);

			//wait until quiesceing is finished
			while(!g_vmx_quiesce_resume_signal);

			//flush EPT TLB
			_vmx_ept_flushmappings();

			spin_lock(&g_vmx_lock_quiesce_resume_counter);
			g_vmx_quiesce_resume_counter++;
			spin_unlock(&g_vmx_lock_quiesce_resume_counter);
			
			xc_cpu->is_quiesced=0;
	}else{
		//we are not in quiesce
		//inject the NMI if it was triggered in guest mode
		
		if(nmiinhvm){
			if(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EXCEPTION_BITMAP) & CPU_EXCEPTION_NMI){
				//TODO: hypapp has chosen to intercept NMI so callback
			}else{ //inject NMI back to partition
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE, 0);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION, (NMI_VECTOR | INTR_TYPE_NMI | INTR_INFO_VALID_MASK));
			}
		}
	}
	
}


void xc_api_hpt_arch_flushcaches(context_desc_t context_desc, bool dosmpflush){
		//xc_cpu_t *xc_cpu = (xc_cpu_t *)context_desc.cpu_desc.xc_cpu;
		//xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
		if(dosmpflush)
			_cpu_arch_x86vmx_quiesce(context_desc);
			
		_vmx_ept_flushmappings();
		
		if(dosmpflush)
			_cpu_arch_x86vmx_endquiesce(context_desc);
}


u64 xc_api_hpt_arch_getentry(context_desc_t context_desc, u64 gpa){
	u64 entry;
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];
	
	xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;  
	
	u64 *hpt = (u64 *)eptdata->vmx_ept_p_tables;
	u32 hpt_index = (u32)gpa / PAGE_SIZE_4K;
	
	entry = hpt[hpt_index];
	
	return entry;
}

void xc_api_hpt_arch_setentry(context_desc_t context_desc, u64 gpa, u64 entry){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];

	xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;  
	
	u64 *hpt = (u64 *)eptdata->vmx_ept_p_tables;
	u32 hpt_index = (u32)gpa / PAGE_SIZE_4K;
	
	hpt[hpt_index] = entry;

	return;
}


u32 xc_api_hpt_arch_getprot(context_desc_t context_desc, u64 gpa){
  xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
  xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];

  xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;  

  u32 pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  u64 *pt = (u64 *)eptdata->vmx_ept_p_tables;
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

void xc_api_hpt_arch_setprot(context_desc_t context_desc, u64 gpa, u32 prottype){
  u32 pfn;
  u64 *pt;
  u32 flags =0;
 xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
 	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];

 
  xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;  
    
  pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  pt = (u64 *)eptdata->vmx_ept_p_tables;
  
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


//walk level 2 page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u64 xc_api_hpt_arch_lvl2pagewalk(context_desc_t context_desc, u64 gva){
  
  //if paging is disabled then physical address is the 
  //supplied virtual address itself
	if( !((xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & CR0_PE) && (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & CR0_PG)) )
		return (u8 *)gpa2hva(gva);

  if((u32)xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR3);
    u32 pdpt_index, pd_index, pt_index, offset;
    u64 paddr;
    pdpt_t kpdpt;
    pdt_t kpd; 
    pt_t kpt; 
    u32 pdpt_entry, pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pdpt_index = pae_get_pdpt_index(gva);
    pd_index = pae_get_pdt_index(gva);
    pt_index = pae_get_pt_index(gva);
    offset = pae_get_offset_4K_page(gva);  

    //grab pdpt entry
    tmp = pae_get_addr_from_32bit_cr3(kcr3);
    kpdpt = (pdpt_t)((u32)tmp); 
    pdpt_entry = kpdpt[pdpt_index];
  
    //grab pd entry
    if( !(pae_get_flags_from_pdpe(pdpt_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;
    tmp = pae_get_addr_from_pdpe(pdpt_entry);
    kpd = (pdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];

    if( !(pae_get_flags_from_pde(pd_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;


    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)pae_get_addr_from_pde(pd_entry);
      kpt = (pt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];

	  if( !(pae_get_flags_from_pte(pt_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;
      
      // find physical page base addr from page table entry 
      paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 2MB page 
      offset = pae_get_offset_big(gva);
      paddr = (u64)pae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u8 *)gpa2hva(paddr);
    
  }else{
    //non-PAE 2 level paging used by guest
    u32 kcr3 = (u32)xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR3);
    u32 pd_index, pt_index, offset;
    u64 paddr;
    npdt_t kpd; 
    npt_t kpt; 
    u32 pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pd_index = npae_get_pdt_index(gva);
    pt_index = npae_get_pt_index(gva);
    offset = npae_get_offset_4K_page(gva);  
  
    // grab pd entry
    tmp = npae_get_addr_from_32bit_cr3(kcr3);
    kpd = (npdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];
  
  
    if( !(npae_get_flags_from_pde(pd_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)npae_get_addr_from_pde(pd_entry);
      kpt = (npt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      if( !(npae_get_flags_from_pte(pt_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;

      // find physical page base addr from page table entry 
      paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 4MB page 
      offset = npae_get_offset_big(gva);
      paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }

    return (u8 *)gpa2hva(paddr);
  }
}


//---------------------------------------------------------------------------------
// Trapmask related APIs

static void _trapmask_operation_trap_io_set(context_desc_t context_desc, xc_hypapp_arch_param_x86vmx_trapio_t trapio){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];

	xc_partition_trapmaskdata_x86vmx_t *xc_partition_trapmaskdata_x86vmx = (xc_partition_trapmaskdata_x86vmx_t *)xc_partition->trapmaskdata;
	u8 *bit_vector = (u8 *)xc_partition_trapmaskdata_x86vmx->vmx_iobitmap_region;
	u32 byte_offset, bit_offset;
	u32 i;

	if(trapio.access_size > sizeof(u32))
		trapio.access_size=sizeof(u32);

	for(i=0; i < trapio.access_size; i++){
		byte_offset = (trapio.portnum+i) / 8;
		bit_offset = (trapio.portnum+i) % 8;
		bit_vector[byte_offset] |= (1 << bit_offset);	
	}
}

static void _trapmask_operation_trap_io_clear(context_desc_t context_desc, xc_hypapp_arch_param_x86vmx_trapio_t trapio){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];

	xc_partition_trapmaskdata_x86vmx_t *xc_partition_trapmaskdata_x86vmx = (xc_partition_trapmaskdata_x86vmx_t *)xc_partition->trapmaskdata;
	u8 *bit_vector = (u8 *)xc_partition_trapmaskdata_x86vmx->vmx_iobitmap_region;
	u32 byte_offset, bit_offset;
	u32 i;

	if(trapio.access_size > sizeof(u32))
		trapio.access_size=sizeof(u32);

	for(i=0; i < trapio.access_size; i++){
		byte_offset = (trapio.portnum+i) / 8;
		bit_offset = (trapio.portnum+i) % 8;
		bit_vector[byte_offset] &= ~((1 << bit_offset));	
	}
}

void xc_api_trapmask_arch_set(context_desc_t context_desc, xc_hypapp_arch_param_t ap){
	switch(ap.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO:{
				_trapmask_operation_trap_io_set(context_desc, ap.param.trapio);
				break;
		}	
	
		default:
			break;
	}

}

void xc_api_trapmask_arch_clear(context_desc_t context_desc, xc_hypapp_arch_param_t ap){
	switch(ap.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO:{
				_trapmask_operation_trap_io_clear(context_desc, ap.param.trapio);
				break;
		}	
	
		default:
			break;
	}

}


//-----------------------------------------------------------------------------------------------
// CPU state related APIs

static void _cpustate_operation_cpugprs_set(context_desc_t context_desc, struct regs x86gprs){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)xc_cpu->cpuarchdata;
	xc_cpuarchdata_x86vmx->x86gprs.edi = x86gprs.edi;
	xc_cpuarchdata_x86vmx->x86gprs.esi = x86gprs.esi;
	xc_cpuarchdata_x86vmx->x86gprs.ebp = x86gprs.ebp;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, x86gprs.esp);
	xc_cpuarchdata_x86vmx->x86gprs.ebx = x86gprs.ebx;
	xc_cpuarchdata_x86vmx->x86gprs.edx = x86gprs.edx;
	xc_cpuarchdata_x86vmx->x86gprs.ecx = x86gprs.ecx;
	xc_cpuarchdata_x86vmx->x86gprs.eax = x86gprs.eax;
}

static struct regs _cpustate_operation_cpugprs_get(context_desc_t context_desc){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)xc_cpu->cpuarchdata;
	struct regs x86gprs;
	
	x86gprs.edi = xc_cpuarchdata_x86vmx->x86gprs.edi;
	x86gprs.esi = xc_cpuarchdata_x86vmx->x86gprs.esi;
	x86gprs.ebp = xc_cpuarchdata_x86vmx->x86gprs.ebp;
	x86gprs.esp = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_RSP);
	x86gprs.ebx = xc_cpuarchdata_x86vmx->x86gprs.ebx;
	x86gprs.edx = xc_cpuarchdata_x86vmx->x86gprs.edx;
	x86gprs.ecx = xc_cpuarchdata_x86vmx->x86gprs.ecx;
	x86gprs.eax = xc_cpuarchdata_x86vmx->x86gprs.eax;

	return x86gprs;
}


static void _cpustate_operation_desc_set(context_desc_t context_desc, xc_hypapp_arch_param_x86vmx_cpustate_desc_t desc){

	//CS, DS, ES, FS, GS and SS segments
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, desc.cs.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, desc.cs.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_LIMIT, desc.cs.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_ACCESS_RIGHTS, desc.cs.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_SELECTOR, desc.ds.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_BASE, desc.ds.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_LIMIT, desc.ds.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_ACCESS_RIGHTS, desc.ds.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_SELECTOR, desc.es.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_BASE, desc.es.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_LIMIT, desc.es.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_ACCESS_RIGHTS, desc.es.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_SELECTOR, desc.fs.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_BASE, desc.fs.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_LIMIT, desc.fs.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_ACCESS_RIGHTS, desc.fs.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_SELECTOR, desc.gs.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_BASE, desc.gs.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_LIMIT, desc.gs.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_ACCESS_RIGHTS, desc.gs.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_SELECTOR, desc.ss.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_BASE, desc.ss.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_LIMIT, desc.ss.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_ACCESS_RIGHTS, desc.ss.access_rights);
	//IDTR
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_BASE, desc.idtr.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_LIMIT, desc.idtr.limit);
	//GDTR
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_BASE, desc.gdtr.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_LIMIT, desc.gdtr.limit);
	//LDTR, unusable
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_BASE, desc.ldtr.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_LIMIT, desc.ldtr.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_SELECTOR, desc.ldtr.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_ACCESS_RIGHTS, desc.ldtr.access_rights);
	//TR, should be usable for VMX to work, but not used by guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_BASE, desc.tr.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_LIMIT, desc.tr.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_SELECTOR, desc.tr.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_ACCESS_RIGHTS, desc.tr.access_rights);
	
	
}

static xc_hypapp_arch_param_x86vmx_cpustate_desc_t _cpustate_operation_desc_get(context_desc_t context_desc){
	xc_hypapp_arch_param_x86vmx_cpustate_desc_t desc;
	
	//CS, DS, ES, FS, GS and SS segments
	desc.cs.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CS_SELECTOR); 		
	desc.cs.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CS_BASE); 			
	desc.cs.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CS_LIMIT); 			
	desc.cs.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CS_ACCESS_RIGHTS); 	
	desc.ds.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_DS_SELECTOR); 		
	desc.ds.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_DS_BASE); 			
	desc.ds.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_DS_LIMIT); 			
	desc.ds.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_DS_ACCESS_RIGHTS); 	
	desc.es.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ES_SELECTOR); 		
	desc.es.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ES_BASE); 			
	desc.es.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ES_LIMIT); 			
	desc.es.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ES_ACCESS_RIGHTS); 	
	desc.fs.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_FS_SELECTOR); 		
	desc.fs.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_FS_BASE); 			
	desc.fs.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_FS_LIMIT); 			
	desc.fs.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_FS_ACCESS_RIGHTS); 	
	desc.gs.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GS_SELECTOR); 		
	desc.gs.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GS_BASE); 			
	desc.gs.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GS_LIMIT); 			
	desc.gs.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GS_ACCESS_RIGHTS); 	
	desc.ss.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SS_SELECTOR); 		
	desc.ss.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SS_BASE); 			
	desc.ss.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SS_LIMIT); 			
	desc.ss.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SS_ACCESS_RIGHTS); 	
	//IDTR
	desc.idtr.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_IDTR_BASE); 		
	desc.idtr.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_IDTR_LIMIT); 		
	//GDTR
	desc.gdtr.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GDTR_BASE); 		
	desc.gdtr.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GDTR_LIMIT); 		
	//LDTR); unusable
	desc.ldtr.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_LDTR_BASE); 		
	desc.ldtr.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_LDTR_LIMIT); 		
	desc.ldtr.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_LDTR_SELECTOR); 	
	desc.ldtr.access_rights =xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_LDTR_ACCESS_RIGHTS); 
	//TR); should be usable for VMX to work; not used by guest
	desc.tr.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_TR_BASE); 			
	desc.tr.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_TR_LIMIT); 			
	desc.tr.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_TR_SELECTOR); 		
	desc.tr.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_TR_ACCESS_RIGHTS); 	
	
	return desc;
}


void xc_api_cpustate_arch_set(context_desc_t context_desc, xc_hypapp_arch_param_t ap){
	switch(ap.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS:{
				_cpustate_operation_cpugprs_set(context_desc, ap.param.cpugprs);
				break;
		}	
	
		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC:{
				_cpustate_operation_desc_set(context_desc, ap.param.desc);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY:{
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, ap.param.activity.rip);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ACTIVITY_STATE, ap.param.activity.activity_state);	
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RFLAGS, ap.param.activity.rflags);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_INTERRUPTIBILITY, ap.param.activity.interruptibility);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS:{
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, ap.param.controlregs.cr0 );
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_SHADOW, ap.param.controlregs.control_cr0_shadow);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, ap.param.controlregs.cr3 );
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, ap.param.controlregs.cr4 );
				break;
		}
	
		default:
			break;
	}

}

xc_hypapp_arch_param_t xc_api_cpustate_arch_get(context_desc_t context_desc, u64 operation){
	xc_hypapp_arch_param_t ap;

	switch(operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS:{
				ap.param.cpugprs = _cpustate_operation_cpugprs_get(context_desc);
				break;
		}	

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC:{
				ap.param.desc = _cpustate_operation_desc_get(context_desc);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY:{
				ap.param.activity.rip = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_RIP); 			
				ap.param.activity.activity_state =xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ACTIVITY_STATE);  	
				ap.param.activity.rflags = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_RFLAGS); 		
				ap.param.activity.interruptibility = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_INTERRUPTIBILITY);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS:{
				ap.param.controlregs.cr0 = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0); 
				ap.param.controlregs.control_cr0_shadow = xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR0_SHADOW);
				ap.param.controlregs.cr3 = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR3); 
				ap.param.controlregs.cr4 = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4); 
				break;
		}
		
		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_INFOREGS:{
				ap.param.inforegs.info_vminstr_error = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
				ap.param.inforegs.info_vmexit_reason = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_REASON);
				ap.param.inforegs.info_vmexit_interrupt_information = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION);
				ap.param.inforegs.info_vmexit_interrupt_error_code = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_INTERRUPT_ERROR_CODE);
				ap.param.inforegs.info_idt_vectoring_information = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IDT_VECTORING_INFORMATION);
				ap.param.inforegs.info_idt_vectoring_error_code = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IDT_VECTORING_ERROR_CODE);
				ap.param.inforegs.info_vmexit_instruction_length = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH);
				ap.param.inforegs.info_vmx_instruction_information = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMX_INSTRUCTION_INFORMATION);
				ap.param.inforegs.info_exit_qualification = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_EXIT_QUALIFICATION);
				ap.param.inforegs.info_io_rcx = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IO_RCX);
				ap.param.inforegs.info_io_rsi = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IO_RSI);
				ap.param.inforegs.info_io_rdi = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IO_RDI);
				ap.param.inforegs.info_io_rip = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IO_RIP);
				ap.param.inforegs.info_guest_linear_address = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_GUEST_LINEAR_ADDRESS);
				ap.param.inforegs.info_guest_paddr_full = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_GUEST_PADDR_FULL);
				break;
		}
	
		default:
			break;
	}
	
	return ap;
}



static void _xc_api_partition_arch_addcpu_setupbasestate(u32 partition_index, u32 cpu_index){
	const u32 vmx_msr_area_msrs[] = {MSR_EFER, MSR_IA32_PAT, MSR_K6_STAR}; //critical MSRs that need to be saved/restored across guest VM switches
	const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));	//count of critical MSRs that need to be saved/restored across VM switches
	u32 lodword, hidword;
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[cpu_index];
	xc_partition_t *xc_partition = &g_xc_primary_partition[partition_index];
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)xc_cpu->cpuarchdata;
	xc_partition_trapmaskdata_x86vmx_t *xc_partition_trapmaskdata_x86vmx = (xc_partition_trapmaskdata_x86vmx_t *)xc_partition->trapmaskdata;
	xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;

	
	//setup host state
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR0, read_cr0());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR4, read_cr4());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR3, read_cr3());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CS_SELECTOR, read_segreg_cs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_DS_SELECTOR, read_segreg_ds());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_ES_SELECTOR, read_segreg_es());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_SELECTOR, read_segreg_fs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_SELECTOR, read_segreg_gs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SS_SELECTOR, read_segreg_ss());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_TR_SELECTOR, read_tr_sel());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GDTR_BASE, xmhf_baseplatform_arch_x86_getgdtbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_IDTR_BASE, xmhf_baseplatform_arch_x86_getidtbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_TR_BASE, xmhf_baseplatform_arch_x86_gettssbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RIP, (u32)xmhf_parteventhub_arch_x86vmx_entry);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RSP, read_esp());
	rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_CS, lodword);
	rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_ESP, (u32)(((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_EIP, (u32)(((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_BASE, (u32) (((u64)hidword << 32) | (u64)lodword) );
	rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_BASE, (u32) (((u64)hidword << 32) | (u64)lodword) );

	//setup default VMX controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_CONTROLS, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);

	//IO bitmap support
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL, (u32)hva2spa((void*)xc_partition_trapmaskdata_x86vmx->vmx_iobitmap_region));
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL, (u32)hva2spa( ((void*)xc_partition_trapmaskdata_x86vmx->vmx_iobitmap_region + PAGE_SIZE_4K) ));
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (1 << 25)) );

	//Critical MSR load/store
	{
		u32 i;
		msr_entry_t *hmsr = (msr_entry_t *)xc_cpuarchdata_x86vmx->vmx_msr_area_host_region;
		msr_entry_t *gmsr = (msr_entry_t *)xc_cpuarchdata_x86vmx->vmx_msr_area_guest_region;

		#ifndef __XMHF_VERIFICATION__
		//store initial values of the MSRs
		for(i=0; i < vmx_msr_area_msrs_count; i++){
			u32 msr, eax, edx;
			msr = vmx_msr_area_msrs[i];						
			rdmsr(msr, &eax, &edx);
			hmsr[i].index = gmsr[i].index = msr;
			hmsr[i].data = gmsr[i].data = ((u64)edx << 32) | (u64)eax;
		}
		#endif

		//host MSR load on exit, we store it ourselves before entry
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, (u32)hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_msr_area_host_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

		//guest MSR load on entry, store on exit
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, (u32)hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_msr_area_guest_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, (u32)hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_msr_area_guest_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);
		
	}


	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EXCEPTION_BITMAP, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR3_TARGET_COUNT, 0);  


	//activate secondary processor controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (1 << 31)) );

	//setup unrestricted guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (1 << 7)) );

	//setup VMCS link pointer
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_FULL, (u32)0xFFFFFFFFUL);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_HIGH, (u32)0xFFFFFFFFUL);
	
	//setup NMI intercept for core-quiescing
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (1 << 3) ) );
	
	//trap access to CR0 fixed 1-bits
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_MASK, ((((xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_SHADOW, xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0));
			
	//trap access to CR4 fixed bits (this includes the VMXE bit)
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_MASK, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_SHADOW, CR4_VMXE);

	//setup memory protection
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (1 <<1) | (1 << 5)) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VPID, 1);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, (hva2spa((void*)eptdata->vmx_ept_pml4_table) | 0x1E) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) & ~(1 << 15) & ~(1 << 16)) );

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
}


bool xc_api_partition_arch_addcpu(u32 partition_index, u32 cpu_index){
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)&g_xc_cpu[cpu_index].cpuarchdata;
	u64 vmcs_phys_addr = hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_vmcs_region);

	//save contents of VMX MSRs as well as MSR EFER and EFCR 
	{
		u32 i;
		u32 eax, edx;
		for(i=0; i < IA32_VMX_MSRCOUNT; i++){
			rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
			xc_cpuarchdata_x86vmx->vmx_msrs[i] = (u64)edx << 32 | (u64) eax;        
		}

		rdmsr(MSR_EFER, &eax, &edx);
		xc_cpuarchdata_x86vmx->vmx_msr_efer = (u64)edx << 32 | (u64) eax;
		rdmsr(MSR_EFCR, &eax, &edx);
		xc_cpuarchdata_x86vmx->vmx_msr_efcr = (u64)edx << 32 | (u64) eax;

		//printf("\nCPU(0x%02x): MSR_EFER=0x%08x%08x", xc_cpu->cpuid, (u32)((u64)xc_cpuarchdata_x86vmx->vmx_msr_efer >> 32), 
		//	(u32)xc_cpuarchdata_x86vmx->vmx_msr_efer);
		//printf("\nCPU(0x%02x): MSR_EFCR=0x%08x%08x", xc_cpu->cpuid, (u32)((u64)xc_cpuarchdata_x86vmx->vmx_msr_efcr >> 32), 
		//	(u32)xc_cpuarchdata_x86vmx->vmx_msr_efcr);
  	}

	//we require unrestricted guest support, bail out if we don't have it
	if( !( (u32)((u64)xc_cpuarchdata_x86vmx->vmx_msrs[IA32_VMX_MSRCOUNT-1] >> 32) & 0x80 ) ){
		printf("\n%s: need unrestricted guest support but did not find any!", __FUNCTION__);
		return false;
	}

	//enable VMX by setting CR4
	asm volatile	(	"mov  %%cr4, %%eax	\r\n"
						"bts  $13, %%eax \r\n"
						"mov  %%eax, %%cr4 \r\n" 
						:
						:
						: "eax" 
					);

	//enter VMX root operation using VMXON
	{
		u32 retval=0;
		u64 vmxonregion_paddr = hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_vmxon_region);
		//set VMCS rev id
		*((u32 *)xc_cpuarchdata_x86vmx->vmx_vmxon_region) = (u32)xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

		asm volatile( "vmxon %1 \n"
				 "jbe vmfail \n"
				 "movl $0x1, %%eax \n" 
				 "movl %%eax, %0 \n"
				 "jmp vmsuccess \n"
				 "vmfail: \n"
				 "movl $0x0, %%eax \n"
				 "movl %%eax, %0 \n"
				 "vmsuccess: \n" 
		   : "=m" (retval)
		   : "m"(vmxonregion_paddr) 
		   : "eax");

		if(!retval){
			printf("\n%s: unable to enter VMX root operation", __FUNCTION__);
			return false;
		}  
	}

	//clear VMCS
	if(!__vmx_vmclear((u64)vmcs_phys_addr))
		return false;
  
	//set VMCS revision id
	*((u32 *)xc_cpuarchdata_x86vmx->vmx_vmcs_region) = (u32)xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

	//load VMPTR
	if(!__vmx_vmptrld((u64)vmcs_phys_addr))
		return false;

	//setup base state of the partition
	_xc_api_partition_arch_addcpu_setupbasestate(partition_index, cpu_index);
		
	return true;
}




//----------------------------------------------------------------------
// start HVM on a given physical core
// on success: this function will not return
// on failure: 1 if a valid error code is present, 0 if no error code, 
// 2 if invalid error info. (should never happen)
//----------------------------------------------------------------------
//static u32 __vmx_start_hvm(void) __attribute__ ((naked)) {
static u32 __vmx_start_hvm(struct regs x86cpugprs) {
	u32 errorcode;
	//struct regs x86cpugprs;
	
	//x86cpugprs.eax = 0;
	//x86cpugprs.ebx = 0;
	//x86cpugprs.ecx = 0;
	//x86cpugprs.edx = 0x80;
	//x86cpugprs.esi = 0;
	//x86cpugprs.edi = 0;
	//x86cpugprs.ebp = 0;

	asm volatile (	"pushal \r\n"
					"movl %1, %%eax\r\n"
					"movl %2, %%ebx\r\n"
					"movl %3, %%ecx\r\n"
					"movl %4, %%edx\r\n"
					"movl %5, %%esi\r\n"
					"movl %6, %%edi\r\n"
					"movl %7, %%ebp\r\n"
					"vmlaunch\r\n"
					"popal \r\n"
					"jc __vmx_start_hvm_failinvalid\r\n"
					"jnz	__vmx_start_hvm_undefinedimplementation	\r\n"
					"movl $0x1, %%eax\r\n"		//VMLAUNCH error, XXX: need to read from VM instruction error field in VMCS
					"movl %%eax, %0 \r\n"
					"jmp __vmx_start_continue \r\n"
					"__vmx_start_hvm_undefinedimplementation:\r\n"
					"movl $0x2, %%eax\r\n"		//violation of VMLAUNCH specs., handle it anyways
					"movl %%eax, %0 \r\n"
					"jmp __vmx_start_continue \r\n"
					"__vmx_start_hvm_failinvalid:\r\n"
					"xorl %%eax, %%eax\r\n"		//return 0 as we have no error code available
					"movl %%eax, %0 \r\n"
					"__vmx_start_continue:\r\n"	
					: "=g"(errorcode)
					: "g" (x86cpugprs.eax), "g" (x86cpugprs.ebx), "g" (x86cpugprs.ecx), "g" (x86cpugprs.edx), "g" (x86cpugprs.esi), "g" (x86cpugprs.edi), "g" (x86cpugprs.ebp)
					: "eax", "ebx", "ecx", "edx", "esi", "edi", "ebp"
				);

	return errorcode;
}


bool xc_api_partition_arch_startcpu(context_desc_t context_desc){
	u32 errorcode;
    struct regs x86cpugprs;
    xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = &g_xc_cpu[context_desc.cpu_desc.cpu_index].cpuarchdata;
    
    x86cpugprs.eax = xc_cpuarchdata_x86vmx->x86gprs.eax;
    x86cpugprs.ebx = xc_cpuarchdata_x86vmx->x86gprs.ebx;
	x86cpugprs.ecx = xc_cpuarchdata_x86vmx->x86gprs.ecx;
	x86cpugprs.edx = xc_cpuarchdata_x86vmx->x86gprs.edx;
	x86cpugprs.esi = xc_cpuarchdata_x86vmx->x86gprs.esi;
	x86cpugprs.edi = xc_cpuarchdata_x86vmx->x86gprs.edi;
	x86cpugprs.ebp = xc_cpuarchdata_x86vmx->x86gprs.ebp;
    
	HALT_ON_ERRORCOND( xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_VMCS_LINK_POINTER_FULL) == 0xFFFFFFFFUL );

	errorcode=__vmx_start_hvm(x86cpugprs);
	HALT_ON_ERRORCOND(errorcode != 2);	//this means the VMLAUNCH implementation violated the specs.

	switch(errorcode){
			case 0:	//no error code, VMCS pointer is invalid
				printf("%s: VMLAUNCH error; VMCS pointer invalid?", __FUNCTION__);
				break;
			case 1:{//error code available, so dump it
				u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
				printf("\n%s: VMLAUNCH error; code=%x", __FUNCTION__, code);
				break;
			}
	}
	
	return false;
}
