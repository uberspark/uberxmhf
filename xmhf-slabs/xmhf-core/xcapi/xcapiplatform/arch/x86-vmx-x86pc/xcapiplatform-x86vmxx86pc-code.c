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

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcapi.h>
#include <xcihub.h>



///////////////////////////////////////////////////////////////////////////////
//platform related core API
typedef struct {
    __attribute__((aligned(4096))) vtd_slpgtbl_t _vtd_slpgtbl;
    bool initialized;
}__attribute__((packed)) xc_partitiondevicetable_t;

__attribute__((aligned(4096))) static  xc_partitiondevicetable_t _partitiondevtable[MAX_PRIMARY_PARTITIONS];

__attribute__((aligned(4096))) static vtd_ret_entry_t _vtd_ret[VTD_RET_MAXPTRS];
__attribute__((aligned(4096))) static vtd_cet_entry_t _vtd_cet[VTD_RET_MAXPTRS][VTD_CET_MAXPTRS];

static vtd_drhd_handle_t vtd_drhd_maxhandle=0;
static u32 vtd_pagewalk_level = VTD_PAGEWALK_NONE;
static bool vtd_initialized = false;

//the quiesce counter, all CPUs except for the one requesting the
//quiesce will increment this when they get their quiesce signal
static u32 g_vmx_quiesce_counter __attribute__(( section(".data") )) = 0;
static u32 g_vmx_lock_quiesce_counter __attribute__(( section(".data") )) = 1;

//the "quiesce" variable, if 1, then we have a quiesce in process
static u32 g_vmx_quiesce __attribute__(( section(".data") )) = 0;;


//static void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(xc_cpu_t *xc_cpu, struct regs *r);
static void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(context_desc_t context_desc, struct regs *r);



static u64 _platform_x86pc_vtd_setup_retcet(void){
    u32 i, j;

    for(i=0; i< VTD_RET_MAXPTRS; i++){
        _vtd_ret[i].qwords[0] = _vtd_ret[i].qwords[1] = 0ULL;
        _vtd_ret[i].fields.p = 1;
        _vtd_ret[i].fields.ctp = ((u64)&_vtd_cet[i] >> 12);

        for(j=0; j < VTD_CET_MAXPTRS; j++){
            _vtd_cet[i][j].qwords[0] = _vtd_cet[i][j].qwords[1] = 0ULL;
        }
    }

    return (u64)&_vtd_ret;
}

//initialize vtd hardware and setup vtd_drhd_maxhandle and _vtd_pagewalk_level
//to appropriate values. if everything went well set vtd_initialized to true
static bool _platform_x86pc_vtd_initialize(void){
    u64 vtd_ret_addr;
	vtd_drhd_handle_t drhd_handle;
	u32 vtd_dmar_table_physical_address=0;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i, b, d, f;

    //if we already setup vtd then simply return true
    if(vtd_initialized)
        return true;

    //initialize partition--device table
    for(i=0; i < MAX_PRIMARY_PARTITIONS; i++)
        _partitiondevtable[i].initialized = false;

	//setup basic RET/CET structure; will initially prevent DMA reads and writes
	//for the entire system
    vtd_ret_addr = _platform_x86pc_vtd_setup_retcet();

	//scan for available DRHD units in the platform
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address)){
        _XDPRINTF_("%s: unable to scan for DRHD units. bailing out!\n", __FUNCTION__);
		return false;
	}

    _XDPRINTF_("%s: maxhandle = %u, dmar table addr=0x%08x\n", __FUNCTION__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);

	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
   		VTD_CAP_REG cap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __FUNCTION__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(drhd_handle) ){
            _XDPRINTF_("%s: error setting up DRHD unit %u. bailing out!\n", __FUNCTION__, drhd_handle);
			return false;
		}

        //read and store DRHD supported page-walk length
        cap.value = xmhfhw_platform_x86pc_vtd_drhd_reg_read(drhd_handle, VTD_CAP_REG_OFF);
        if(cap.bits.sagaw & 0x2){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_3LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 3-level page-walk\n", __FUNCTION__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __FUNCTION__);
                HALT();
            }
        }

        if(cap.bits.sagaw & 0x4){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_4LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 4-level page-walk\n", __FUNCTION__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __FUNCTION__);
                HALT();
            }
        }


		//set DRHD root entry table
		if(!xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(drhd_handle, vtd_ret_addr))
			return false;

		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;

		//enable VT-d translation
		xmhfhw_platform_x86pc_vtd_drhd_enable_translation(drhd_handle);

		//disable PMRs now (since DMA protection is active via translation)
		xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(drhd_handle);

		_XDPRINTF_("%s: Successfully setup DRHD unit %u\n", __FUNCTION__, drhd_handle);
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhfhw_sysmemaccess_writeu32(vtd_dmar_table_physical_address, 0UL);


    _XDPRINTF_("%s: final page-walk level=%u\n", __FUNCTION__, vtd_pagewalk_level);

    vtd_initialized = true;

    return true;
}

static vtd_slpgtbl_handle_t _platform_x86pc_vtd_setup_slpgtbl(u32 partition_index){
    vtd_slpgtbl_handle_t retval = {0, 0};
    u32 i, j, k, paddr=0;

    //sanity check partition index
    if(partition_index >= MAX_PRIMARY_PARTITIONS){
        _XDPRINTF_("%s: Error: partition_index >= MAX_PRIMARY_PARTITIONS. bailing out!\n", __FUNCTION__);
        return retval;
    }

    //setup device memory access for the partition
    _partitiondevtable[partition_index]._vtd_slpgtbl.pml4t[0].fields.r = 1;
    _partitiondevtable[partition_index]._vtd_slpgtbl.pml4t[0].fields.w = 1;
    _partitiondevtable[partition_index]._vtd_slpgtbl.pml4t[0].fields.slpdpt = ((u64)&_partitiondevtable[partition_index]._vtd_slpgtbl.pdpt >> 12);

    for(i=0; i < PAE_PTRS_PER_PDPT; i++){
        _partitiondevtable[partition_index]._vtd_slpgtbl.pdpt[i].fields.r = 1;
        _partitiondevtable[partition_index]._vtd_slpgtbl.pdpt[i].fields.w = 1;
        _partitiondevtable[partition_index]._vtd_slpgtbl.pdpt[i].fields.slpdt = ((u64)&_partitiondevtable[partition_index]._vtd_slpgtbl.pdt[i] >> 12);

        for(j=0; j < PAE_PTRS_PER_PDT; j++){
            _partitiondevtable[partition_index]._vtd_slpgtbl.pdt[i][j].fields.r = 1;
            _partitiondevtable[partition_index]._vtd_slpgtbl.pdt[i][j].fields.w = 1;
            _partitiondevtable[partition_index]._vtd_slpgtbl.pdt[i][j].fields.slpt = ((u64)&_partitiondevtable[partition_index]._vtd_slpgtbl.pt[i][j] >> 12);

            for(k=0; k < PAE_PTRS_PER_PT; k++){
                _partitiondevtable[partition_index]._vtd_slpgtbl.pt[i][j][k].fields.r = 1;
                _partitiondevtable[partition_index]._vtd_slpgtbl.pt[i][j][k].fields.w = 1;
                _partitiondevtable[partition_index]._vtd_slpgtbl.pt[i][j][k].fields.pageaddr = ((u64)paddr >> 12);
                paddr += PAGE_SIZE_4K;
            }
        }
    }

    retval.addr_vtd_pml4t = _partitiondevtable[partition_index]._vtd_slpgtbl.pml4t;
    retval.addr_vtd_pdpt = _partitiondevtable[partition_index]._vtd_slpgtbl.pdpt;

    return retval;
}



//shutdown platform
void xc_api_platform_arch_shutdown(context_desc_t context_desc){
	//shut VMX off, else CPU ignores INIT signal!
	asm volatile("vmxoff \r\n");
	write_cr4(read_cr4() & ~(CR4_VMXE));

	//fall back on generic x86 reboot
	xmhf_baseplatform_arch_x86_reboot();
}


xc_platformdevice_desc_t xc_api_platform_arch_initializeandenumeratedevices(context_desc_t context_desc){
    xc_platformdevice_desc_t result;
    u32 b, d, f;

    result.desc_valid = false;
    result.numdevices = 0;

    //initialize vtd hardware (if it has not been initialized already)
    if(!_platform_x86pc_vtd_initialize())
        return result;

    //enumerate PCI bus to find out all the devices
	//bus numbers range from 0-255, device from 0-31 and function from 0-7
	for(b=0; b < PCI_BUS_MAX; b++){
		for(d=0; d < PCI_DEVICE_MAX; d++){
			for(f=0; f < PCI_FUNCTION_MAX; f++){
				u32 vendor_id, device_id;

				//read device and vendor ids, if no device then both will be 0xFFFF
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_VENDOR_ID, sizeof(u16), &vendor_id);
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_DEVICE_ID, sizeof(u16), &device_id);
				if(vendor_id == 0xFFFF && device_id == 0xFFFF)
					break;

                result.arch_desc[result.numdevices].pci_bus=b;
                result.arch_desc[result.numdevices].pci_device=d;
                result.arch_desc[result.numdevices].pci_function=f;
                result.arch_desc[result.numdevices].vendor_id=vendor_id;
                result.arch_desc[result.numdevices].device_id=device_id;

                result.numdevices++;
			}
		}
	}

    result.desc_valid = true;
    return result;
}


bool xc_api_platform_arch_allocdevices_to_partition(context_desc_t context_desc, xc_platformdevice_desc_t device_descs){
	vtd_drhd_handle_t drhd_handle;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i;

    if(!vtd_initialized)
        return false;


    //initialize partition device page tables (if it has not been initialized already)
    if(!_partitiondevtable[context_desc.partition_desc.partition_index].initialized){
        vtd_slpgtbl_handle = _platform_x86pc_vtd_setup_slpgtbl(context_desc.partition_desc.partition_index);

        if(vtd_slpgtbl_handle.addr_vtd_pml4t == 0 &&
            vtd_slpgtbl_handle.addr_vtd_pdpt == 0){
            _XDPRINTF_("%s: unable to initialize vt-d pagetables for partition %u\n", __FUNCTION__, context_desc.partition_desc.partition_index);
            return false;
        }

        _partitiondevtable[context_desc.partition_desc.partition_index].initialized = true;
    }


    for(i=0; i < device_descs.numdevices; i++){
        u32 b=device_descs.arch_desc[i].pci_bus;
        u32 d=device_descs.arch_desc[i].pci_device;
        u32 f=device_descs.arch_desc[i].pci_function;

        //sanity check b, d, f triad
        if ( !(b < PCI_BUS_MAX &&
               d < PCI_DEVICE_MAX &&
               f < PCI_FUNCTION_MAX) )
            return false;

        //b is our index into ret
        // (d* PCI_FUNCTION_MAX) + f = index into the cet
        if(vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.slptptr = ((u64)_partitiondevtable[context_desc.partition_desc.partition_index]._vtd_slpgtbl.pml4t >> 12);
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.aw = 2; //4-level
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.did = (context_desc.partition_desc.partition_index + 1); //domain
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.p = 1; //present
        }else if (vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.slptptr = ((u64)_partitiondevtable[context_desc.partition_desc.partition_index]._vtd_slpgtbl.pdpt >> 12);
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.aw = 1; //3-level
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.did = (context_desc.partition_desc.partition_index + 1); //domain
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.p = 1; //present
        }else{ //unknown page walk length, fail
            return false;
        }
    }


	//invalidate vtd caches
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;
	}

    return true;
}


bool xc_api_platform_arch_deallocdevices_from_partition(context_desc_t context_desc, xc_platformdevice_desc_t device_descs){
	vtd_drhd_handle_t drhd_handle;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i;

    if(!vtd_initialized)
        return false;

    for(i=0; i < device_descs.numdevices; i++){
        u32 b=device_descs.arch_desc[i].pci_bus;
        u32 d=device_descs.arch_desc[i].pci_device;
        u32 f=device_descs.arch_desc[i].pci_function;

        //sanity check b, d, f triad
        if ( !(b < PCI_BUS_MAX &&
               d < PCI_DEVICE_MAX &&
               f < PCI_FUNCTION_MAX) )
            return false;

        //b is our index into ret
        // (d* PCI_FUNCTION_MAX) + f = index into the cet
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].qwords[0] = 0;
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].qwords[1] = 0;
    }

	//invalidate vtd caches
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;
	}

    return true;
}


//**
//quiescing handler for #NMI (non-maskable interrupt) exception event
void xc_coreapi_arch_eventhandler_nmiexception(struct regs *r){
	//xc_cpu_t *xc_cpu;
	context_desc_t context_desc;

	context_desc = xc_api_partition_getcontextdesc(xmhf_baseplatform_arch_x86_getcpulapicid());
	if(context_desc.cpu_desc.cpu_index == XC_PARTITION_INDEX_INVALID || context_desc.partition_desc.partition_index == XC_PARTITION_INDEX_INVALID){
		_XDPRINTF_("%s: invalid partition/cpu context. Halting!\n", __FUNCTION__);
		HALT();
	}
	xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(context_desc, r);
}

//*
//quiescing handler for #NMI (non-maskable interrupt) exception event
//note: we are in atomic processsing mode for this "xc_cpu"
//static void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(xc_cpu_t *xc_cpu, struct regs *r){
static void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(context_desc_t context_desc, struct regs *r){
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
            //call hypapp quiesce handler
            XMHF_SLAB_CALL(xmhf_hypapp_handlequiesce(context_desc));

			//increment quiesce counter
			spin_lock(&g_vmx_lock_quiesce_counter);
			g_vmx_quiesce_counter++;
			spin_unlock(&g_vmx_lock_quiesce_counter);

	}else{
		//we are not in quiesce
		//inject the NMI if it was triggered in guest mode

		if(nmiinhvm){
			if(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EXCEPTION_BITMAP) & CPU_EXCEPTION_NMI){
				//TODO: hypapp has chosen to intercept NMI so callback
			}else{ //inject NMI back to partition
				if( (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_INTERRUPTIBILITY) == 0) &&
       				(xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ACTIVITY_STATE) == 0) ){
                    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE, 0);
                    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION, (NMI_VECTOR | INTR_TYPE_NMI | INTR_INFO_VALID_MASK));
				}
			}
		}
	}

}

static void _vmx_send_quiesce_signal(void){
  u32 prev_icr_high_value;

  prev_icr_high_value = xmhfhw_sysmemaccess_readu32((0xFEE00000 + 0x310));

  xmhfhw_sysmemaccess_writeu32((0xFEE00000 + 0x310), (0xFFUL << 24)); //send to all but self
  xmhfhw_sysmemaccess_writeu32((0xFEE00000 + 0x300), 0x000C0400UL); //send NMI

  while( xmhfhw_sysmemaccess_readu32((0xFEE00000 + 0x310)) & 0x00001000 );

  xmhfhw_sysmemaccess_writeu32((0xFEE00000 + 0x310), prev_icr_high_value);
}


void xc_api_platform_arch_quiescecpus_in_partition(context_desc_t context_desc){

        g_vmx_quiesce_counter=0;						//reset quiesce counter
        g_vmx_quiesce=1;  								//we are now processing quiesce

        _vmx_send_quiesce_signal();				        //send all the other CPUs the quiesce signal
        //_XDPRINTF_("%s(%u): sent quiesce signal...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index);
        //wait until all other CPUs are done with the flushing
        while(g_vmx_quiesce_counter < (context_desc.partition_desc.numcpus-1) );

        g_vmx_quiesce=0;                                //done processing quiesce
}

