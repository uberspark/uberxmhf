// appmain.c
// sechyp application main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

#include "./include/lockdown.h"
#include "./include/acpi.h"


u32 acpi_control_portnum=0;
u32 currentenvironment = LDN_ENV_UNTRUSTED_SIGNATURE; //default to untrusted env.

                            
u32 sechyp_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb){
  LDNPB *pldnPb;
  printf("\nCPU(0x%02x): Lockdown initiaizing...", vcpu->id);
  
	//ACPI initialization
	ACPIInitializeRegisters();

  acpi_control_portnum = (u32)PM1_CNTa;
  
  printf("\nCPU(0x%02x): Lockdown; ACPI control port=0x%08x",
    vcpu->id, acpi_control_portnum);
  
  //set I/O port intercept for ACPI control port
  sechyp_iopm_set_write(vcpu, acpi_control_portnum, 2); //16-bit port

  //grab the ldn parameter block from verifier, this tells us the
  //destination environment characteristics
  //TODO: verifier integration, for now we just take it from the apb
  ASSERT( apb->optionalmodule_size > 0 );
  pldnPb = (LDNPB *) apb->optionalmodule_ptr;
  printf("\nCPU(0x%02x): destination environment signature = 0x%08x", 
      vcpu->id, pldnPb->signature);
  currentenvironment = pldnPb->signature;  
  
  return APP_INIT_SUCCESS;  //successful
}

u32 sechyp_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, 
  u32 portnum, u32 access_type, u32 access_size){
  
  if(access_type == IO_TYPE_OUT && portnum == acpi_control_portnum && 
      access_size == IO_SIZE_WORD && ((u16)r->eax & (u16)(1 << 13)) ){
      printf("\nCPU(0x%02x): Lockdown; ACPI SLEEP_EN signal caught. resetting...",
          vcpu->id);
      sechyp_reboot();
      //we should never get here
      HALT();  
  }
  
  return APP_IOINTERCEPT_CHAIN; //chain and do the required I/O    
}