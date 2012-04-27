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

// appmain.c
// emhf application main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h>

#include <lockdown.h>
#include <lockdown-acpi.h>
#include <ata-atapi.h>
#include <approvedexec.h>

#if defined(__LDN_HYPERSWITCHING__)
u32 acpi_control_portnum=0;
#endif

u32 LDN_ENV_PHYSICALMEMORYLIMIT=0; //max physical memory address permissible
																		//for the guest environment
 
u32 currentenvironment = LDN_ENV_UNTRUSTED_SIGNATURE; //default to untrusted env.


/*
//---setup 2M pages in EPT
//---TODO: we need to move this to emhf core at some point
void vmx_setupEPT2M(VCPU *vcpu){
#if 0
  //step-1: tie in EPT PML4 structures
	//note: the default memory type (usually WB) should be determined using 
	//IA32_MTRR_DEF_TYPE_MSR. If MTRR's are not enabled (really?)
	//then all default memory is type UC (uncacheable)
  u64 *pml4_table, *pdp_table, *pd_table, *p_table;
	u32 i, j, k, paddr=0;
	
	pml4_table = (u64 *)vcpu->vmx_vaddr_ept_pml4_table;
	pml4_table[0] = (u64) (__hva2spa__((u32)vcpu->vmx_vaddr_ept_pdp_table) | 0x7); 
	
	pdp_table = (u64 *)vcpu->vmx_vaddr_ept_pdp_table;
		
	for(i=0; i < 4; i++){
		pdp_table[i] = (u64) ( __hva2spa__((u32)vcpu->vmx_vaddr_ept_pd_tables + (4096 * i)) | 0x7 );
		pd_table = (u64 *)  ((u32)vcpu->vmx_vaddr_ept_pd_tables + (4096 * i)) ;
		
		for(j=0; j < 512; j++){
	 		u32 memorytype = vmx_getmemorytypeforphysicalpage(vcpu, (u64)paddr);
			pd_table[j] = (u64) (paddr)  | ((u64)memorytype << 3) | (u64)0x87 ;	//2M page 
			paddr += PAGE_SIZE_2M;
		}
	}
#else
	#define	GUEST_MEMLIMIT	(0x70000000)	//1.75GB
  u64 *pd_table;
	u32 i, paddr=0;
	
	pd_table = (u64 *)  ((u32)vcpu->vmx_vaddr_ept_pd_tables) ;
	for(i=0; i< 2048; i++){
		if(paddr != 0){
			//if(paddr > GUEST_MEMLIMIT)
			//	break;
		
			{
				u32 memorytype = vmx_getmemorytypeforphysicalpage(vcpu, (u64)paddr);
				pd_table[i] = (u64) (paddr)  | ((u64)memorytype << 3) | (u64)0x87 ;	//2M page 
			}
		}
			
	  paddr += PAGE_SIZE_2M;
	}
#endif
}
*/



//------------------------------------------------------------------------------
//app main                            
u32 emhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb){
	LDNPB *pldnPb;
	
	//we only perform setup on the BSP
	if(!vcpu->isbsp){	
		printf("\nCPU(0x%02x): Lockdown initiaizing. Skipping init on AP.", vcpu->id);
		return APP_INIT_SUCCESS;
	}

	printf("\nCPU(0x%02x): BSP. Lockdown initiaizing...", vcpu->id);
	
	//setup guest environment physical memory size
	LDN_ENV_PHYSICALMEMORYLIMIT = (apb->runtimephysmembase - PAGE_SIZE_2M); 


#if defined(__LDN_HYPERSWITCHING__)  
	//ACPI initialization
	ACPIInitializeRegisters();

  acpi_control_portnum = (u32)PM1_CNTa;
  
  printf("\nCPU(0x%02x): Lockdown; ACPI control port=0x%08x",
    vcpu->id, acpi_control_portnum);
  
  //set I/O port intercept for ACPI control port
  emhf_partition_legacyIO_setprot(vcpu, acpi_control_portnum, 2, PART_LEGACYIO_NOACCESS); //16-bit port
#endif

#if defined(__LDN_HYPERPARTITIONING__)
  //set IDE port intercepts for hyper-partitioning
 
  emhf_partition_legacyIO_setprot(vcpu, ATA_COMMAND(ATA_BUS_PRIMARY), 1, PART_LEGACYIO_NOACCESS); //8-bit port
  emhf_partition_legacyIO_setprot(vcpu, ATA_SECTOR_COUNT(ATA_BUS_PRIMARY), 1, PART_LEGACYIO_NOACCESS); //8-bit port
  emhf_partition_legacyIO_setprot(vcpu, ATA_LBALOW(ATA_BUS_PRIMARY), 1, PART_LEGACYIO_NOACCESS); //8-bit port
  emhf_partition_legacyIO_setprot(vcpu, ATA_LBAMID(ATA_BUS_PRIMARY), 1, PART_LEGACYIO_NOACCESS); //8-bit port
  emhf_partition_legacyIO_setprot(vcpu, ATA_LBAHIGH(ATA_BUS_PRIMARY), 1, PART_LEGACYIO_NOACCESS); //8-bit port

  printf("\nCPU(0x%02x): Lockdown; Setup hyperpartitioning on \
    ATA/SATA device at 0x%08x", vcpu->id, ATA_BUS_PRIMARY);

#endif

	//grab the ldn parameter block from verifier, this tells us the
	//destination environment characteristics
	//TODO: verifier integration, for now we just take it from the apb
	if(apb->optionalmodule_size == 0){
		//if we don't have an optional module then load the untrusted
		//environment
		currentenvironment = LDN_ENV_UNTRUSTED_SIGNATURE;
		printf("\nCPU(0x%02x): booting UNTRUSTED environment...", vcpu->id);
	}else{
		//an optional module was specified, so load the trusted 
		//environment
		pldnPb = (LDNPB *) apb->optionalmodule_ptr;
		currentenvironment = LDN_ENV_TRUSTED_SIGNATURE;
		
		//sanity check we have a good TE parameter block
		if(pldnPb->signature != LDN_ENV_TRUSTED_SIGNATURE){
			printf("\nCPU(0x%02x): unknown destination environment signature (0x%08x), halting!", 
				vcpu->id, pldnPb->signature);
			HALT();
		}

	    printf("\nCPU(0x%02x): booting TRUSTED environment...", vcpu->id);
	}


	//check if we are going to the trusted environment, if so enable
	//approved execution and mask off any network interfaces
	if(currentenvironment == LDN_ENV_TRUSTED_SIGNATURE){
		//enable approved execution
		#if defined(__LDN_APPROVEDEXEC__)
			approvedexec_setup(vcpu, apb);
		#endif
    
		//mask off all network interfaces by interposing on PCI bus accesses
		#if defined(__LDN_SSLPA__)
			emhf_iopm_set_write(vcpu, PCI_CONFIG_DATA_PORT, 2); //16-bit port
		#endif
	}else{	//we are going to run the untrusted environment
		ASSERT( currentenvironment == LDN_ENV_UNTRUSTED_SIGNATURE);
	
		/*//TODO:make EPT entries such that they map 2M pages for the untrusted
		//environment in order to achieve greatest speedup during EPT
		//translation
		vmx_setupEPT2M(vcpu);
		emhf_hwpgtbl_flushall(vcpu);
		printf("\nCPU(0x%02x): setup 2M EPT pages");*/
	}
  
  //test purposes, force currentenvironment to by UNTRUSTED.
  //this should prevent the bootsector from reading any of the
  //partition sectors
  //currentenvironment = LDN_ENV_UNTRUSTED_SIGNATURE;
  
  return APP_INIT_SUCCESS;  //successful
}



extern u32 hp(VCPU *vcpu, struct regs *r, u32 portnum, u32 access_type, u32 access_size);



#if defined(__LDN_SSLPA__)
struct __machine_networkdevices {
  u32 bus;
  u32 device;
  u32 function;
} machine_networkdevices[] = {
  LDN_MACHINE_NETWORKDEVICES
};

//returns 1 if device specified by the bus:device:function triad
//is of networking class
u32 sslpa_isnetworkdevice(u32 bus, u32 device, u32 function){
 u32 i;
 for(i=0; i < (sizeof(machine_networkdevices)/sizeof(struct __machine_networkdevices)); i++){
  if(machine_networkdevices[i].bus == bus &&
    machine_networkdevices[i].device == device &&
    machine_networkdevices[i].function == function)
    return 1;
 }
  
 return 0;
}

#endif

u32 emhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, 
  u32 portnum, u32 access_type, u32 access_size){
#if defined(__LDN_HYPERSWITCHING__)  
		u32 acpi_sleep_en;
#endif	  

#if defined(__LDN_HYPERSWITCHING__)  
 
  if(vcpu->cpu_vendor == CPU_VENDOR_AMD)
	acpi_sleep_en = (u16)(((struct vmcb_struct *)vcpu->vmcb_vaddr_ptr)->rax) & (u16)(1 << 13);
  else
	acpi_sleep_en = ((u16)r->eax & (u16)(1 << 13));

  //printf("\nCPU(0x%02x): Lockdown type=%u, portnum=0x%08x, size=%u, sleep_en=%u", 
  //	vcpu->id, access_type, portnum, access_size, acpi_sleep_en);
  
  if(access_type == IO_TYPE_OUT && portnum == acpi_control_portnum && 
      access_size == IO_SIZE_WORD && acpi_sleep_en ){
      printf("\nCPU(0x%02x): Lockdown; ACPI SLEEP_EN signal caught. resetting firmware...",
          vcpu->id);
      
			#if defined (__LDN_TEST_FWRESET__)			
			{
				extern void initunrestrictedguestVMCS(VCPU *vcpu);
				extern void dumpVMCS(VCPU *vcpu);
				
				ASSERT(vcpu->guest_unrestricted);
				memcpy((void *)0x7c00, (void *)&test_bootsectorbuffer, 512);
				memcpy((void *)0x00000000, (void *)&test_first1024, 1024);				
				initunrestrictedguestVMCS(vcpu);
				printf("\nCPU(0x%02x): Now restarting guest again...", vcpu->id);
				r->eax=0;
				r->ebx=0;
				r->ecx=0;
				r->edx=0x80;
				r->esi=0;
				r->edi=0;
				r->ebp=0;
				vcpu->vmcs.info_vmexit_instruction_length=0; //needed since when we return APP_IOINTERCEPT_SKIP
						//islayer will add this to RIP
				hw_disk_printpciconf();
				hw_disk_restorepciconf();
				hw_disk_printpciconf();
				hw_vga_reset();
				printf("\nCPU(0x%02x): sent VGA compatible reset sequence...", vcpu->id);
				hw_disk_reset();
				printf("\nCPU(0x%02x): sent ATA/ATAPI compatible reset sequence...", vcpu->id);
				//dumpVMCS(vcpu);
				//HALT();
				return APP_IOINTERCEPT_SKIP;
			}	
			#elif defined (__LDN_TEST_MLOAD__)
			{
				extern void initunrestrictedguestVMCS(VCPU *vcpu);
				extern void dumpVMCS(VCPU *vcpu);
				
				ASSERT(vcpu->guest_unrestricted);
				initunrestrictedguestVMCS(vcpu);
				printf("\nCPU(0x%02x): Now restarting guest again...", vcpu->id);
				vcpu->vmcs.info_vmexit_instruction_length=0; //needed since when we return APP_IOINTERCEPT_SKIP
						//islayer will add this to RIP
				setuplinuxboot(vcpu, (u32)&test_mload_vmlinuz_buffer, test_mload_vmlinuz_size, 
					(u32)&test_mload_initrd_buffer, test_mload_initrd_size);
				printf("\nCPU(0x%02x): manual loading of linux vmlinuz/initramfs done.", vcpu->id);
				//hw_disk_restorepciconf();
				//printf("\nCPU(0x%02x): restored PCI configuration of disk controller..", vcpu->id);
				hw_vga_reset();
				printf("\nCPU(0x%02x): sent VGA compatible reset sequence...", vcpu->id);
				return APP_IOINTERCEPT_SKIP;
			}
			#else
				emhf_baseplatform_reboot(vcpu);
			#endif
      //we should never get here
      HALT();  
  }

#else //__LDN_HYPERSWITCHING__ 
	(void)vcpu;
	(void)r;
	(void)portnum;
	(void)access_type;
	(void)access_size;
#endif //__LDN_HYPERSWITCHING__

#if defined(__LDN_HYPERPARTITIONING__)  
  if( portnum == ATA_COMMAND(ATA_BUS_PRIMARY) ||
		portnum == ATA_SECTOR_COUNT(ATA_BUS_PRIMARY) ||
		portnum == ATA_LBALOW(ATA_BUS_PRIMARY) ||
		portnum == ATA_LBAMID(ATA_BUS_PRIMARY) ||
		portnum == ATA_LBAHIGH(ATA_BUS_PRIMARY)
		){
			u32 retval;
			//printf("\nATA IO port access:0x%04x", (u16)portnum);
			retval = hp(vcpu, r, portnum, access_type, access_size);
			return retval;
	}
#endif

#if defined(__LDN_SSLPA__)
  if(portnum == PCI_CONFIG_DATA_PORT){
    //printf("\nCPU(0x%02x): PCI DATA acc, size=%u, type=%u", 
    //  vcpu->id, access_size, access_type);  
    pci_config_reg_addr_t pci_addr;
    pci_addr.bytes = inl((u32)PCI_CONFIG_ADDR_PORT);
    
    if(sslpa_isnetworkdevice(pci_addr.fields.bus, pci_addr.fields.device, 
        pci_addr.fields.function)) {
      if(access_type == IO_TYPE_IN){
        u32 retval;
        printf("\nCPU(0x%02x): N/W device accessed, denying... (t=%u, s=%u, offset=0x%08x)", 
          vcpu->id, access_type, access_size, pci_addr.fields.offset);

        if(pci_addr.fields.offset == 0)
          retval=0xFFFFFFFFUL;  //no device present
        else
          retval=0; //null value for all other configuration registers
        
        ASSERT( (access_size == IO_SIZE_BYTE) || (access_size == IO_SIZE_WORD) ||
            (access_size == IO_SIZE_DWORD) );
        switch(access_size){
          case IO_SIZE_BYTE: r->eax &= 0xFFFFFF00UL; r->eax |= (u8)retval; break;
          case IO_SIZE_WORD: r->eax &= 0xFFFF0000UL; r->eax |= (u16)retval; break;
          case IO_SIZE_DWORD: r->eax = retval; break;
        }
        
        return APP_IOINTERCEPT_SKIP;
       
      }else{
        printf("\nCPU(0x%02x): N/W device forced write? HALT! (t=%u, s=%u, offset=0x%08x)", 
          vcpu->id, access_type, access_size, pci_addr.fields.offset);
        HALT();
      }
    }
  
  }
#endif

  
  return APP_IOINTERCEPT_CHAIN; //chain and do the required I/O    
}

//----------------------------------------------------------------------
// nested (extended) page fault handler 
// used to implement approved execution
//----------------------------------------------------------------------
u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
      struct regs *r,
      u64 gpa, u64 gva, u64 violationcode){
	(void)r;

#if defined(__LDN_APPROVEDEXEC__)
	if(currentenvironment == LDN_ENV_TRUSTED_SIGNATURE)
	  return( approvedexec_handleevent(vcpu, r, gpa, gva, violationcode) );
#endif	//__LDN_APPROVEDEXEC__

	//we never handle nested (extended) page faults in the untrusted
	//environment
	printf("\nCPU(0x%02x): Unhandled HW page-fault!", 
		vcpu->id);
  	printf("\nCPU(0x%02x): gva=0x%08x, gpa=0x%08x, errorcode=0x%08x", 
		vcpu->id, (u32)gva, (u32)gpa, (u32)violationcode);
  	printf("\nCPU(0x%02x): current gpa protection is: 0x%08x", 
		emhf_memprot_getprot(vcpu, gpa));
	printf("\nCPU(0x%02x): Halting!"); 
	HALT();
	return APP_ERROR;	//we never get here
}
//----------------------------------------------------------------------



void emhf_app_handleshutdown(VCPU *vcpu, struct regs *r){
	(void)r;
	emhf_baseplatform_reboot(vcpu);
}



//returns APP_SUCCESS if we handled the hypercall else APP_ERROR
u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r){
			u32 status=APP_SUCCESS;
			
		(void)r;
		(void)vcpu;

		return status;
}      
