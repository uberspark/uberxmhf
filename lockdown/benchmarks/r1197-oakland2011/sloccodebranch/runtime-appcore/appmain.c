// appmain.c
// emhf application main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

#include "./include/lockdown.h"
#include "./include/acpi.h"
#include "./include/ata-atapi.h"

#if defined(__LDN_HYPERSWITCHING__)
u32 acpi_control_portnum=0;
#endif

u32 LDN_ENV_PHYSICALMEMORYLIMIT=0; //max physical memory address permissible
																		//for the guest environment
 
u32 currentenvironment = LDN_ENV_UNTRUSTED_SIGNATURE; //default to untrusted env.



//------------------------------------------------------------------------------
//memcmp implementation
int memcmp (const unsigned char *str1, const unsigned char *str2, int count){
  register const unsigned char *s1 = (const unsigned char*)str1;
  register const unsigned char *s2 = (const unsigned char*)str2;

  while (count-- > 0)
    {
      if (*s1++ != *s2++)
	  return s1[-1] < s2[-1] ? -1 : 1;
    }
  return 0;
}







//---setup 2M pages in EPT
//---TODO: we need to move this to emhf core at some point
void vmx_setupEPT2M(VCPU *vcpu){
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
}




//------------------------------------------------------------------------------
//app main                            
u32 emhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb){
  LDNPB *pldnPb;
  printf("\nCPU(0x%02x): Lockdown initiaizing...", vcpu->id);

	//setup guest environment physical memory size
	LDN_ENV_PHYSICALMEMORYLIMIT = apb->runtimephysmembase; 





#if defined(__LDN_HYPERSWITCHING__)  
	//ACPI initialization
	ACPIInitializeRegisters();

  acpi_control_portnum = (u32)PM1_CNTa;
  
  printf("\nCPU(0x%02x): Lockdown; ACPI control port=0x%08x",
    vcpu->id, acpi_control_portnum);
  
  //set I/O port intercept for ACPI control port
  emhf_iopm_set_write(vcpu, acpi_control_portnum, 2); //16-bit port
#endif

#if defined(__LDN_HYPERPARTITIONING__)
  //set IDE port intercepts for hyper-partitioning
  emhf_iopm_set_write(vcpu, ATA_COMMAND(ATA_BUS_PRIMARY), 1); //8-bit port
  emhf_iopm_set_write(vcpu, ATA_SECTOR_COUNT(ATA_BUS_PRIMARY), 1); //8-bit port
  emhf_iopm_set_write(vcpu, ATA_LBALOW(ATA_BUS_PRIMARY), 1); //8-bit port
  emhf_iopm_set_write(vcpu, ATA_LBAMID(ATA_BUS_PRIMARY), 1); //8-bit port
  emhf_iopm_set_write(vcpu, ATA_LBAHIGH(ATA_BUS_PRIMARY), 1); //8-bit port
#endif

  //grab the ldn parameter block from verifier, this tells us the
  //destination environment characteristics
  //TODO: verifier integration, for now we just take it from the apb
  ASSERT( apb->optionalmodule_size > 0 );
  pldnPb = (LDNPB *) apb->optionalmodule_ptr;
  printf("\nCPU(0x%02x): destination environment signature = 0x%08x", 
      vcpu->id, pldnPb->signature);
  currentenvironment = pldnPb->signature;  

  if(currentenvironment == LDN_ENV_TRUSTED_SIGNATURE)
    printf("\nCPU(0x%02x): booting TRUSTED environment...", vcpu->id);
  else
    printf("\nCPU(0x%02x): booting UNTRUSTED environment...", vcpu->id);

  //check if we are going to the trusted environment, if so enable
  //approved execution and mask off any network interfaces
  if(currentenvironment == LDN_ENV_TRUSTED_SIGNATURE){
    //enable approved execution
    #if defined(__LDN_APPROVEDEXEC__)
    {
      u32 endpfn = __runtimephysicalbase / PAGE_SIZE_4K;
      u32 i;
      //setup all guest physical memory region to non-executable to
      //start with
      for(i=0; i < endpfn; i++)
        emhf_hwpgtbl_setprot(vcpu, (i*PAGE_SIZE_4K), (emhf_hwpgtbl_getprot(vcpu, (i*PAGE_SIZE_4K)) & ~HWPGTBL_FLAG_EXECUTE));     
  
      emhf_hwpgtbl_flushall(vcpu);  //flush all NPT/EPT mappings
      printf("\nCPU(0x%02x): Setup trusted execution and flushed all HW pagetable mappings...");
    }
    #endif
    
    //mask off all network interfaces by interposing on PCI bus accesses
    #if defined(__LDN_SSLPA__)
    emhf_iopm_set_write(vcpu, PCI_CONFIG_DATA_PORT, 2); //16-bit port
    #endif
  
  }else{	//we are going to run the untrusted environment
  	ASSERT( currentenvironment == LDN_ENV_UNTRUSTED_SIGNATURE);
	
		//TODO:make EPT entries such that they map 2M pages for the untrusted
		//environment in order to achieve greatest speedup during EPT
		//translation
		vmx_setupEPT2M(vcpu);
		emhf_hwpgtbl_flushall(vcpu);
		printf("\nCPU(0x%02x): setup 2M EPT pages");
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
  if(access_type == IO_TYPE_OUT && portnum == acpi_control_portnum && 
      access_size == IO_SIZE_WORD && ((u16)r->eax & (u16)(1 << 13)) ){
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
#endif

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

#if defined (__NESTED_PAGING__)                       
extern u32 approvedexec_handleevent(VCPU *vcpu, struct regs *r, 
  u64 gpa, u64 gva, u64 violationcode);

//for now this always returns APP_SUCCESS
u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
      struct regs *r,
      u64 gpa, u64 gva, u64 violationcode){
#if defined(__LDN_APPROVEDEXEC__)
  if(currentenvironment == LDN_ENV_TRUSTED_SIGNATURE){
	  return( approvedexec_handleevent(vcpu, r, gpa, gva, violationcode) );
	}else{
	  printf("\nCPU(0x%02x): Fatal, got HW pgfault in untrusted should never happen", vcpu->id);
  	printf("\nCPU(0x%02x): gva=0x%08x, gpa=0x%08x, code=0x%08x", vcpu->id,
			(u32)gva, (u32)gpa, (u32)violationcode);
  	printf("\nprot is: 0x%016llx", emhf_hwpgtbl_getprot(vcpu, gpa));
		HALT();
	
	}
#else
  printf("\nCPU(0x%02x): HW pgtbl handling feature unimplemented. Halting!", vcpu->id);
  printf("\nCPU(0x%02x): gva=0x%08x, gpa=0x%08x, code=0x%08x", vcpu->id,
			(u32)gva, (u32)gpa, (u32)violationcode);
  printf("\nprot is: 0x%016llx", emhf_hwpgtbl_getprot(vcpu, gpa));
	HALT();
#endif
}
#endif


void emhf_app_handleshutdown(VCPU *vcpu, struct regs *r){
				emhf_reboot();
}




//returns APP_SUCCESS if we handled the hypercall else APP_ERROR
u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r){
			u32 status=APP_SUCCESS;


			return status;
}      