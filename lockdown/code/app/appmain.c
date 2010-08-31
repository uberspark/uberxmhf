// appmain.c
// sechyp application main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

#include "./include/lockdown.h"
#include "./include/acpi.h"
#include "./include/ata-atapi.h"

#if defined(__LDN_HYPERSWITCHING__)
u32 acpi_control_portnum=0;
#endif


u32 currentenvironment = LDN_ENV_UNTRUSTED_SIGNATURE; //default to untrusted env.

                            
u32 sechyp_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb){
  LDNPB *pldnPb;
  printf("\nCPU(0x%02x): Lockdown initiaizing...", vcpu->id);


#if defined(__LDN_HYPERSWITCHING__)  
	//ACPI initialization
	ACPIInitializeRegisters();

  acpi_control_portnum = (u32)PM1_CNTa;
  
  printf("\nCPU(0x%02x): Lockdown; ACPI control port=0x%08x",
    vcpu->id, acpi_control_portnum);
  
  //set I/O port intercept for ACPI control port
  sechyp_iopm_set_write(vcpu, acpi_control_portnum, 2); //16-bit port
#endif

#if defined(__LDN_HYPERPARTITIONING__)
  //set IDE port intercepts for hyper-partitioning
  sechyp_iopm_set_write(vcpu, ATA_COMMAND(ATA_BUS_PRIMARY), 1); //8-bit port
  sechyp_iopm_set_write(vcpu, ATA_SECTOR_COUNT(ATA_BUS_PRIMARY), 1); //8-bit port
  sechyp_iopm_set_write(vcpu, ATA_LBALOW(ATA_BUS_PRIMARY), 1); //8-bit port
  sechyp_iopm_set_write(vcpu, ATA_LBAMID(ATA_BUS_PRIMARY), 1); //8-bit port
  sechyp_iopm_set_write(vcpu, ATA_LBAHIGH(ATA_BUS_PRIMARY), 1); //8-bit port
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
    sechyp_iopm_set_write(vcpu, PCI_CONFIG_DATA_PORT, 2); //16-bit port
    #endif
  
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

u32 sechyp_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, 
  u32 portnum, u32 access_type, u32 access_size){

#if defined(__LDN_HYPERSWITCHING__)  
  if(access_type == IO_TYPE_OUT && portnum == acpi_control_portnum && 
      access_size == IO_SIZE_WORD && ((u16)r->eax & (u16)(1 << 13)) ){
      printf("\nCPU(0x%02x): Lockdown; ACPI SLEEP_EN signal caught. resetting firmware...",
          vcpu->id);
      sechyp_reboot();
      //we should never get here
      HALT();  
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

                       
extern u32 approvedexec_handleevent(VCPU *vcpu, struct regs *r, 
  u64 gpa, u64 gva, u64 violationcode);

//for now this always returns APP_SUCCESS
u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
      struct regs *r,
      u64 gpa, u64 gva, u64 violationcode){
#if defined(__LDN_APPROVEDEXEC__)
  return( approvedexec_handleevent(vcpu, r, gpa, gva, violationcode) );
#else
  printf("\nCPU(0x%02x): HW pgtbl handling feature unimplemented. Halting!", vcpu->id);
  HALT();
#endif
}
