// appmain.c
// emhf application main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h>

#include <lockdown.h>
#include <lockdown-acpi.h>
#include <ata-atapi.h>

#if defined(__LDN_HYPERSWITCHING__)
u32 acpi_control_portnum=0;
#endif

u32 LDN_ENV_PHYSICALMEMORYLIMIT=0; //max physical memory address permissible
																		//for the guest environment
 
u32 currentenvironment = LDN_ENV_UNTRUSTED_SIGNATURE; //default to untrusted env.

#if 0
//linux hibernation related
#define	LDN_HYPERCALL_HIB_READWRITE	(0xDEADF00D)
#define LDN_HYPERCALL_HIB_TOTALPAGES (0xF00DDEAD)
#define HIB_READ		0x0
#define HIB_WRITE		0x1
#define TEST_MLOAD_HIB_BUFFER_SIZE (512*1024*1024)
u8 test_mload_hib_buffer[TEST_MLOAD_HIB_BUFFER_SIZE];	//512MB test buffer
struct swsusp_header {
	u8 reserved[PAGE_SIZE_4K - 20 - 4 - 4];
	u32	image;
	u32 flags;
	u8 orig_sig[10];
	u8 sig[10];
} __attribute__((packed));

struct swsusp_header *swsusp_header;


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
#endif

#if defined (__LDN_TEST_FWRESET__)
//our boot-sector buffer to restore between switches
u8 test_bootsectorbuffer[512];
u8 test_first1024[1024]; //the first 1K of low memory
#endif

#if defined (__LDN_TEST_MLOAD__)
	#define MAX_VMLINUZ_BUFFER_SIZE		(8*1024*1024)		//8MB max vmlinuz size (compressed)
	#define MAX_INITRD_BUFFER_SIZE		(16*1024*1024)	//16MB max initrd size (compressed)

	u8 test_mload_vmlinuz_buffer[MAX_VMLINUZ_BUFFER_SIZE];
	u8 test_mload_initrd_buffer[MAX_INITRD_BUFFER_SIZE];
	u32 test_mload_vmlinuz_size;
	u32 test_mload_initrd_size;
#endif




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
  printf("\nCPU(0x%02x): Lockdown initiaizing...", vcpu->id);

	//setup guest environment physical memory size
	LDN_ENV_PHYSICALMEMORYLIMIT = apb->runtimephysmembase; 

#if defined (__LDN_TEST_MLOAD__)
	//we use the app param. block fields as below
	//bootsector_ptr and bootsector_size now become vmlinuz_ptr and vmlinuz_size
	//optionalmodule_ptr and optionalmodule_size become initramfs_ptr and initramfs_size
	
	//sanity checks
	ASSERT( apb->bootsector_size > 0 && apb->bootsector_size < MAX_VMLINUZ_BUFFER_SIZE ); 
	ASSERT( apb->optionalmodule_size > 0 && apb->optionalmodule_size < MAX_INITRD_BUFFER_SIZE );
	
	printf("\nCPU(0x%02x): vmlinuz b=0x%08x, size=%u bytes", vcpu->id,
			apb->bootsector_ptr, apb->bootsector_size);
	printf("\nCPU(0x%02x): initramfs b=0x%08x, size=%u bytes", vcpu->id,
			apb->optionalmodule_ptr, apb->optionalmodule_size);
	
	memcpy((void *)test_mload_vmlinuz_buffer, (void *)apb->bootsector_ptr, apb->bootsector_size);
	memcpy((void *)test_mload_initrd_buffer, (void *)apb->optionalmodule_ptr, apb->optionalmodule_size);
	printf("\nCPU(0x%02x): copied vmlinuz and initramfs to internal buffer.");
	test_mload_vmlinuz_size = apb->bootsector_size;
	test_mload_initrd_size = apb->optionalmodule_size;

	//hw_disk_savepciconf();
	//printf("\nCPU(0x%02x): saved PCI configuration of disk controller..", vcpu->id);
	
	setuplinuxboot(vcpu, (u32)&test_mload_vmlinuz_buffer, test_mload_vmlinuz_size, 
		(u32)&test_mload_initrd_buffer, test_mload_initrd_size);
	printf("\nCPU(0x%02x): manual loading of linux vmlinuz/initramfs done.", vcpu->id);
	
	//clear our hibernation RAM space
	printf("\nCPU(0x%02x): clearing HIB RAM...", vcpu->id);
	memset((void *)&test_mload_hib_buffer, 0, TEST_MLOAD_HIB_BUFFER_SIZE);
	printf("\nCPU(0x%02x): HIB RAM cleared.", vcpu->id);

	//setup SWSUSP header at offset 0
	ASSERT(sizeof(struct swsusp_header) == PAGE_SIZE_4K);
	swsusp_header = (struct swsusp_header *)&test_mload_hib_buffer;
	swsusp_header->image=2;
	swsusp_header->orig_sig[0]='S';
	swsusp_header->orig_sig[1]='W';
	swsusp_header->orig_sig[2]='A';
	swsusp_header->orig_sig[3]='P';
	swsusp_header->orig_sig[4]='S';
	swsusp_header->orig_sig[5]='P';
	swsusp_header->orig_sig[6]='A';
	swsusp_header->orig_sig[7]='C';
	swsusp_header->orig_sig[8]='E';
	swsusp_header->orig_sig[9]='2';
	swsusp_header->sig[0]='S';
	swsusp_header->sig[1]='W';
	swsusp_header->sig[2]='A';
	swsusp_header->sig[3]='P';
	swsusp_header->sig[4]='S';
	swsusp_header->sig[5]='P';
	swsusp_header->sig[6]='A';
	swsusp_header->sig[7]='C';
	swsusp_header->sig[8]='E';
	swsusp_header->sig[9]='2';
#endif


#if defined (__LDN_TEST_FWRESET__)
	//some sanity checks
	ASSERT( apb->bootsector_size == 512 );
	#if defined (__MP_VERSION__)
		#error TEST code is not designed to work with MP version (yet?)
	#endif
	//copy the boot-sector into our buffer
	memcpy((void *)&test_bootsectorbuffer, (void *)apb->bootsector_ptr, apb->bootsector_size);
	printf("\nCPU(0x%02x): saved guest boot-sector, sig=0x%02x%02x", vcpu->id, test_bootsectorbuffer[510], 
				test_bootsectorbuffer[511]);
	memcpy((void *)&test_first1024, (void *)0x00000000, 1024);
	printf("\nCPU(0x%02x): saved low 1K of mem", vcpu->id);
	
	//initialize pci subsystem
	if(!pci_initialize()){
		printf("\nCPU(0x%02x): fatal error, could not initialze PCI subsystem. Halting!", vcpu->id);
		HALT();
	}
	
	hw_disk_printpciconf();
	hw_disk_savepciconf();
	hw_disk_restorepciconf();
	hw_disk_printpciconf();
	hw_vga_reset();
	printf("\nCPU(0x%02x): sent VGA compatible reset sequence...", vcpu->id);
	hw_disk_reset();
	printf("\nCPU(0x%02x): sent ATA/ATAPI compatible reset sequence...", vcpu->id);
	
#endif


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


		/*#if 0
		//TODO:make EPT entries such that they map 2M pages for the untrusted
		//environment in order to achieve greatest speedup during EPT
		//translation
		vmx_setupEPT2M(vcpu);
		emhf_hwpgtbl_flushall(vcpu);
		printf("\nCPU(0x%02x): setup 2M EPT pages");
		#endif*/
  
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
  	printf("\nprot is: 0x%08x", emhf_memprot_getprot(vcpu, gpa));
		HALT();
	
	}
#else
  (void)r;
  printf("\nCPU(0x%02x): HW pgtbl handling feature unimplemented. Halting!", vcpu->id);
  printf("\nCPU(0x%02x): gva=0x%08x, gpa=0x%08x, code=0x%08x", vcpu->id,
			(u32)gva, (u32)gpa, (u32)violationcode);
  printf("\nprot is: 0x%08x", emhf_memprot_getprot(vcpu, gpa));
	HALT();
#endif

  while(1);
}
#endif


void emhf_app_handleshutdown(VCPU *vcpu, struct regs *r){
			#if defined (__LDN_TEST_MLOAD__)
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
				return;
			}
			#else
				(void)r;
				emhf_baseplatform_reboot(vcpu);
			#endif
}




//returns APP_SUCCESS if we handled the hypercall else APP_ERROR
u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r){
			u32 status=APP_SUCCESS;
			
		(void)r;
		(void)vcpu;


/*			u32 call_id= (u32)r->eax;
      if(call_id == 0xDEADBEEF){
        printf("\nCPU(0x%02x): marker message.", vcpu->id);
      }else if(call_id == LDN_HYPERCALL_HIB_READWRITE){
				switch(r->edx){
					case HIB_READ:
						//ebx is the offset starting from 0 in multiples of 8
						//r->edi is the physical address of the page, so sanity check it
		      	if(r->ebx == 0)
							printf("\nCPU(0x%02x): HIB(R), o=%u, s=%u, rw=%u, v=0x%08x, p=0x%08x", vcpu->id,
								r->ebx, r->ecx, r->edx, r->esi, r->edi);

						ASSERT( (u32)(u32 *)emhf_smpguest_walk_pagetables(vcpu, r->esi) == r->edi );
						memcpy( (void *)r->edi,
										(void *) ((u32)&test_mload_hib_buffer + ((r->ebx/8)*PAGE_SIZE_4K) ),
									 PAGE_SIZE_4K);
						break;

					case HIB_WRITE:
						//ebx is the offset starting from 0 in multiples of 8
		      	if(r->ebx == 0)
							printf("\nCPU(0x%02x): HIB(W), o=%u, s=%u, rw=%u, v=0x%08x, p=0x%08x", vcpu->id,
									r->ebx, r->ecx, r->edx, r->esi, r->edi);

						ASSERT( (u32)(u32 *)emhf_smpguest_walk_pagetables(vcpu, r->esi) == r->edi );

						memcpy( (void *) ((u32)&test_mload_hib_buffer + ((r->ebx/8)*PAGE_SIZE_4K) ),
									(void *)r->edi, PAGE_SIZE_4K);
						break;
				
					default:
						printf("\nCPU(0x%02x): error(halt), HIB(RW) unknown rw value!", vcpu->id);
						HALT();	
				}
					
			}else if(call_id == LDN_HYPERCALL_HIB_TOTALPAGES){
				printf("\nCPU(0x%02x): HIB(TP), total pages=%u", vcpu->id,
					r->ebx);
				ASSERT( (r->ebx * PAGE_SIZE_4K) < TEST_MLOAD_HIB_BUFFER_SIZE );
			}else{ 	
				status=APP_ERROR; //unknown hypercall
      }*/

			return status;
}      
