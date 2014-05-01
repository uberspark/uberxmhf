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
//note: we are in atomic processsing mode for this "xc_cpu"
void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(xc_cpu_t *xc_cpu, struct regs *r){
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

static void _trapmask_operation_trap_io_set(context_desc_t context_desc, u16 port, u8 size){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];

	xc_partition_trapmaskdata_x86vmx_t *xc_partition_trapmaskdata_x86vmx = (xc_partition_trapmaskdata_x86vmx_t *)xc_partition->trapmaskdata;
	u8 *bit_vector = (u8 *)xc_partition_trapmaskdata_x86vmx->vmx_iobitmap_region;
	u32 byte_offset, bit_offset;
	u32 i;

	if(size > sizeof(u32))
		size=sizeof(u32);

	for(i=0; i < size; i++){
		byte_offset = (port+i) / 8;
		bit_offset = (port+i) % 8;
		bit_vector[byte_offset] |= (1 << bit_offset);	
	}
}

static void _trapmask_operation_trap_io_clear(context_desc_t context_desc, u16 port, u8 size){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];

	xc_partition_trapmaskdata_x86vmx_t *xc_partition_trapmaskdata_x86vmx = (xc_partition_trapmaskdata_x86vmx_t *)xc_partition->trapmaskdata;
	u8 *bit_vector = (u8 *)xc_partition_trapmaskdata_x86vmx->vmx_iobitmap_region;
	u32 byte_offset, bit_offset;
	u32 i;

	if(size > sizeof(u32))
		size=sizeof(u32);

	for(i=0; i < size; i++){
		byte_offset = (port+i) / 8;
		bit_offset = (port+i) % 8;
		bit_vector[byte_offset] &= ~((1 << bit_offset));	
	}
}

void xc_api_trapmask_arch_set(context_desc_t context_desc, xc_hypapp_arch_param_t trapmaskparams){
	switch(trapmaskparams.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO:{
				//params[0]=16-bit port number, params[1]=size in bytes - 1,2 or 4
				_trapmask_operation_trap_io_set(context_desc, (u16)trapmaskparams.params[0], (u8)trapmaskparams.params[1]);
				break;
		}	
	
		default:
			break;
	}

}

void xc_api_trapmask_arch_clear(context_desc_t context_desc, xc_hypapp_arch_param_t trapmaskparams){
	switch(trapmaskparams.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO:{
				//params[0]=16-bit port number, params[1]=size in bytes - 1,2 or 4
				_trapmask_operation_trap_io_clear(context_desc, (u16)trapmaskparams.params[0], (u8)trapmaskparams.params[1]);
				break;
		}	
	
		default:
			break;
	}

}


//-----------------------------------------------------------------------------------------------
// CPU state related APIs

static void _cpustate_operation_cpugprs_set(context_desc_t context_desc, struct regs *x86gprs){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)xc_cpu->cpuarchdata;
	xc_cpuarchdata_x86vmx->x86gprs.edi = x86gprs->edi;
	xc_cpuarchdata_x86vmx->x86gprs.esi = x86gprs->esi;
	xc_cpuarchdata_x86vmx->x86gprs.ebp = x86gprs->ebp;
	xc_cpuarchdata_x86vmx->x86gprs.esp = x86gprs->esp;
	xc_cpuarchdata_x86vmx->x86gprs.ebx = x86gprs->ebx;
	xc_cpuarchdata_x86vmx->x86gprs.edx = x86gprs->edx;
	xc_cpuarchdata_x86vmx->x86gprs.ecx = x86gprs->ecx;
	xc_cpuarchdata_x86vmx->x86gprs.eax = x86gprs->eax;
}

static void _cpustate_operation_cpugprs_get(context_desc_t context_desc, struct regs *x86gprs){
	xc_cpu_t *xc_cpu = (xc_cpu_t *)&g_xc_cpu[context_desc.cpu_desc.cpu_index];
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)xc_cpu->cpuarchdata;
	x86gprs->edi = xc_cpuarchdata_x86vmx->x86gprs.edi;
	x86gprs->esi = xc_cpuarchdata_x86vmx->x86gprs.esi;
	x86gprs->ebp = xc_cpuarchdata_x86vmx->x86gprs.ebp;
	x86gprs->esp = xc_cpuarchdata_x86vmx->x86gprs.esp;
	x86gprs->ebx = xc_cpuarchdata_x86vmx->x86gprs.ebx;
	x86gprs->edx = xc_cpuarchdata_x86vmx->x86gprs.edx;
	x86gprs->ecx = xc_cpuarchdata_x86vmx->x86gprs.ecx;
	x86gprs->eax = xc_cpuarchdata_x86vmx->x86gprs.eax;
}

void xc_api_cpustate_arch_set(context_desc_t context_desc, xc_hypapp_arch_param_t cpustateparams){
	switch(cpustateparams.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS:{
				//params[0]..[7] = x86 general purpose registers - edi,esi,ebp,esp,ebx,edx,ecx,eax
				struct regs x86gprs;
				x86gprs.edi = cpustateparams.params[0];
				x86gprs.esi = cpustateparams.params[1];
				x86gprs.ebp = cpustateparams.params[2];
				x86gprs.esp = cpustateparams.params[3];
				x86gprs.ebx = cpustateparams.params[4];
				x86gprs.edx = cpustateparams.params[5];
				x86gprs.ecx = cpustateparams.params[6];
				x86gprs.eax = cpustateparams.params[7];
				_cpustate_operation_cpugprs_set(context_desc, &x86gprs);
				break;
		}	
	
		default:
			break;
	}

}

xc_hypapp_arch_param_t xc_api_cpustate_arch_get(context_desc_t context_desc, u64 operation){
	xc_hypapp_arch_param_t cpustateparams;

	switch(operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS:{
				//params[0]..[7] = x86 general purpose registers - edi,esi,ebp,esp,ebx,edx,ecx,eax
				struct regs x86gprs;
				_cpustate_operation_cpugprs_get(context_desc, &x86gprs);
				cpustateparams.params[0] = x86gprs.edi;
				cpustateparams.params[1] = x86gprs.esi;
				cpustateparams.params[2] = x86gprs.ebp;
				cpustateparams.params[3] = x86gprs.esp;
				cpustateparams.params[4] = x86gprs.ebx;
				cpustateparams.params[5] = x86gprs.edx;
				cpustateparams.params[6] = x86gprs.ecx;
				cpustateparams.params[7] = x86gprs.eax;
				break;
		}	
	
		default:
			break;
	}
	
	return cpustateparams;
}


