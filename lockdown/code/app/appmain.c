// appmain.c
// sechyp application main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

#include <acpi.h>
#include <libsechyp.h>

// a placeholder for now...
u32 sechyp_app_main(VCPU *vcpu){
  u32 acpi_control_portnum, acpi_status_portnum;
  
  printf("\nCPU(0x%02x): Lockdown initiaizing...", vcpu->id);
  
	//ACPI initialization
	ACPIInitializeRegisters();

  acpi_control_portnum = (u32)PM1_CNTa;
  acpi_status_portnum = (u32)PM1a_STS;
  
  printf("\nCPU(0x%02x): Lockdown; ACPI cp=0x%08x, sp=0x%08x",
    vcpu->id, acpi_control_portnum, acpi_status_portnum);
  
  //set I/O port intercept for ACPI control port
  sechyp_iopm_set_write(vcpu, acpi_control_portnum, 2); //16-bit port
  
  return APP_INIT_SUCCESS;  //successful
}

u32 sechyp_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, 
  u32 portnum, u32 access_type, u32 access_size){
  
  printf("\nCPU(0x%02x): App, IO intercept, p=0x%04x, at=0x%02x, size=0x%08x",
      vcpu->id, portnum, access_type, access_size);
  printf("\nCPU(0x%02x): HALT!", vcpu->id);
  HALT();
    
  return APP_IOINTERCEPT_CHAIN; //chain and do the required I/O    
    
}