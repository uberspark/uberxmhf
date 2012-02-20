//------------------------------------------------------------------------------
// hp_sdisk_ata.c
// hyper-partitioning implementation for multiple partitions on a single
// ata disk
// author: amit vasudevan (amitvasudevan@acm.org) 

#include <emhf.h>

#include <lockdown.h>
#include <ata-atapi.h>

//extern struct vmcb_struct *win_vmcb;
//extern u32 guest_RAX;

u8 ata_sector_count_buf[2], ata_lbalow_buf[2], ata_lbamid_buf[2];
u8 ata_lbahigh_buf[2];

u32 ata_sector_count_index=0;
u32 ata_lbalow_index=0;
u32 ata_lbamid_index=0;
u32 ata_lbahigh_index=0;


u64 LBA48_TO_CPU64(u8 bits63_56, u8 bits55_48, u8 bits47_40, u8 bits39_32, u8 bits31_24, u8 bits23_16, u8 bits15_8, u8 bits7_0) {
	return		( (u64) ( 
			((u64)bits63_56 << 56) | ((u64)bits55_48 << 48) | ((u64)bits47_40 << 40) | 
			((u64)bits39_32 << 32) | ((u64)bits31_24 << 24) | ((u64)bits23_16 << 16) | 
			((u64)bits15_8 << 8) | (u64)bits7_0 
		) );
}

void CPU64_TO_LBA48(u64 value, u8 *bits47_40, u8 *bits39_32, 
	u8 *bits31_24, u8 *bits23_16, u8 *bits15_8, u8 *bits7_0){

	*bits47_40 = (u8) ( ((u64)value & 0x0000FF0000000000ULL) >> 40 );
	*bits39_32 = (u8) ( ((u64)value & 0x000000FF00000000ULL) >> 32 );
	*bits31_24 = (u8) ( ((u64)value & 0x00000000FF000000ULL) >> 24 );
	*bits23_16 = (u8) ( ((u64)value & 0x0000000000FF0000ULL) >> 16 );
	*bits15_8 =  (u8) ( ((u64)value & 0x000000000000FF00ULL) >> 8 );
	*bits7_0 =   (u8) ( ((u64)value & 0x00000000000000FFULL) >> 0 );
}

u32 LBA28_TO_CPU32(u8 bits27_24, u8 bits23_16, u8 bits15_8, u8 bits7_0){
 return ( (u32) ( ((u32)bits27_24 << 24) | 
 		((u32)bits23_16 << 16) | ((u32)bits15_8 << 8) | (u32)bits7_0 ) );
}


void CPU32_TO_LBA28(u32 value, u8 *bits27_24, 
	u8 *bits23_16, u8 *bits15_8, u8 *bits7_0){

	*bits27_24 = (u8) ( ((u32)value & 0x0F000000ULL) >> 24 );
	*bits23_16 = (u8) ( ((u64)value & 0x00FF0000ULL) >> 16 );
	*bits15_8 =  (u8) ( ((u64)value & 0x0000FF00ULL) >> 8 );
	*bits7_0 =   (u8) ( ((u64)value & 0x000000FFULL) >> 0 );
}

//this is an array of known sectors that access should be allowed
//irrespective of the environment we are in. these include the MBR and
//start sectors of extended partitions if any.
u32 hp_allowedsectors[] = {
  LDN_ALLOWED_SECTORS
};


//check if a given LBA is out of bounds of the partition
//returns 1 if out of bounds, else 0
extern u32 currentenvironment;

u32 check_if_LBA_outofbounds(u64 lbaaddr){
	u32 i;
  ASSERT(currentenvironment == LDN_ENV_TRUSTED_SIGNATURE ||
      currentenvironment == LDN_ENV_UNTRUSTED_SIGNATURE);

#if 0  
  //check if the given LBA falls into one of the allowed sectors list
  for(i=0; i< (sizeof(hp_allowedsectors)/sizeof(u32)); i++){
    if(hp_allowedsectors[i] == (u32)lbaaddr)
      return 0; //not out of bounds
  }
      
  if(currentenvironment == LDN_ENV_TRUSTED_SIGNATURE){
	 //if we are operating in the TRUSTED environment, restrict all sector
	 //accesses to the trusted partition and the first 63 sectors which is
   //the legacy bootmanager area
   if( LDN_OUTOFBOUNDS_CHECK )  
			return 0; //not out of bounds
	 else
			return 1; //out of bounds
	}else{
   //if we are operating in the UNTRUSTED environment, prevent any accesses
   //to the trusted partition
   if( (((u64)lbaaddr >= (u64)LDN_ENV_TRUSTED_STARTSECTOR)
	   && ((u64)lbaaddr <= (u64)LDN_ENV_TRUSTED_ENDSECTOR))
		  )
			return 1; //out of bounds
	 else
			return 0; //not out of bounds 
  
  }
  
#else
	(void)lbaaddr;
	(void)i;
	return 0; //not out of bounds 

#endif  
}

//return guest EAX value 
u32 hp_getguesteaxvalue(VCPU *vcpu, struct regs *r){
		if(vcpu->cpu_vendor == CPU_VENDOR_AMD)
			return (u32) ((struct vmcb_struct *)vcpu->vmcb_vaddr_ptr)->rax;
		else
			return r->eax;
}

//returns APP_IOINTERCEPT_SKIP or APP_IOINTERCEPT_CHAIN
u32 hp(VCPU *vcpu, struct regs *r, u32 portnum, u32 access_type, u32 access_size){
	u8 command, temp;
	u64 lba48addr;
	u32 lba28addr;
	
	if (access_size != IO_SIZE_BYTE){
		printf("\nCPU(0x%02x): Non-byte access to IDE port unsupported. HALT!", vcpu->id);
		HALT();
	}

	if(access_type == IO_TYPE_IN)	//IN, we simply chain
		return APP_IOINTERCEPT_CHAIN;

	//check for correct disk
	temp=inb(ATA_DRIVE_SELECT(ATA_BUS_PRIMARY));
	if(temp & 0x10)	//slave, so simply chain
		return APP_IOINTERCEPT_CHAIN;

	switch(portnum){
		case ATA_SECTOR_COUNT(ATA_BUS_PRIMARY):
			if(ata_sector_count_index > 1){
				ata_sector_count_buf[0]=ata_sector_count_buf[1];
				ata_sector_count_buf[1]=(u8)hp_getguesteaxvalue(vcpu, r);
			}else{
				ata_sector_count_buf[ata_sector_count_index]=(u8)hp_getguesteaxvalue(vcpu, r);
			}
			ata_sector_count_index++;
			return(APP_IOINTERCEPT_CHAIN);
		
		case ATA_LBALOW(ATA_BUS_PRIMARY):
			if(ata_lbalow_index > 1){
				ata_lbalow_buf[0]=ata_lbalow_buf[1];
				ata_lbalow_buf[1]=(u8)hp_getguesteaxvalue(vcpu, r);
			}else{
				ata_lbalow_buf[ata_lbalow_index]=(u8)hp_getguesteaxvalue(vcpu, r);
			}
			ata_lbalow_index++;
			return(APP_IOINTERCEPT_CHAIN);
			
		case ATA_LBAMID(ATA_BUS_PRIMARY):
			if(ata_lbamid_index > 1){
				ata_lbamid_buf[0]=ata_lbamid_buf[1];
				ata_lbamid_buf[1]=(u8)hp_getguesteaxvalue(vcpu, r);
			}else{
				ata_lbamid_buf[ata_lbamid_index]=(u8)hp_getguesteaxvalue(vcpu, r);
			}
			ata_lbamid_index++;
			return(APP_IOINTERCEPT_CHAIN);

		case ATA_LBAHIGH(ATA_BUS_PRIMARY):
			if(ata_lbahigh_index > 1){
				ata_lbahigh_buf[0]=ata_lbahigh_buf[1];
				ata_lbahigh_buf[1]=(u8)hp_getguesteaxvalue(vcpu, r);
			}else{
				ata_lbahigh_buf[ata_lbahigh_index]=(u8)hp_getguesteaxvalue(vcpu, r);
			}
			ata_lbahigh_index++;
			return(APP_IOINTERCEPT_CHAIN);
	
		case ATA_COMMAND(ATA_BUS_PRIMARY):
			command = (u8)hp_getguesteaxvalue(vcpu, r);
			if(command == CMD_READ_DMA_EXT || command == CMD_WRITE_DMA_EXT){
				lba48addr = LBA48_TO_CPU64(0x00, 0x00, ata_lbahigh_buf[0], 
					ata_lbamid_buf[0], ata_lbalow_buf[0], ata_lbahigh_buf[1], 
					ata_lbamid_buf[1], ata_lbalow_buf[1]);

				//[DBG]
				printf("\nATA R/W DMA EXT: 0x%02x (count=%02x%02x, lba=%u)", 
				command, ata_sector_count_buf[0], ata_sector_count_buf[1],
					(u32)lba48addr);

				//check if we are out of bounds
				if(check_if_LBA_outofbounds(lba48addr)){
					printf("\nATA R/W DMA EXT (OOB): 0x%02x (count=%02x%02x, lba=%02x%02x%02x%02x%02x%02x)", 
						command, ata_sector_count_buf[0], ata_sector_count_buf[1],
						ata_lbahigh_buf[0], ata_lbamid_buf[0], ata_lbalow_buf[0],
						ata_lbahigh_buf[1], ata_lbamid_buf[1], ata_lbalow_buf[1]);
					//convert the access to the "null" sector	
					CPU64_TO_LBA48((u64)LDN_NULL_SECTOR, &ata_lbahigh_buf[0], 
					&ata_lbamid_buf[0], &ata_lbalow_buf[0], &ata_lbahigh_buf[1], 
					&ata_lbamid_buf[1], &ata_lbalow_buf[1]);
	
				//resend the new LBA and sector count addresses
				outb (ata_sector_count_buf[0], ATA_SECTOR_COUNT(ATA_BUS_PRIMARY));
				outb (ata_lbalow_buf[0], ATA_LBALOW(ATA_BUS_PRIMARY));
				outb (ata_lbamid_buf[0], ATA_LBAMID(ATA_BUS_PRIMARY));
				outb (ata_lbahigh_buf[0], ATA_LBAHIGH(ATA_BUS_PRIMARY));
				outb (ata_sector_count_buf[1], ATA_SECTOR_COUNT(ATA_BUS_PRIMARY));
				outb (ata_lbalow_buf[1], ATA_LBALOW(ATA_BUS_PRIMARY));
				outb (ata_lbamid_buf[1], ATA_LBAMID(ATA_BUS_PRIMARY));
				outb (ata_lbahigh_buf[1], ATA_LBAHIGH(ATA_BUS_PRIMARY));
	
				}				
				
				
				
				ata_sector_count_index=0;
				ata_lbalow_index = ata_lbamid_index = ata_lbahigh_index=0;
				ata_sector_count_buf[0] = ata_sector_count_buf[1] = 0;
				ata_lbalow_buf[0] = ata_lbalow_buf[1] = 0;
				ata_lbamid_buf[0] = ata_lbamid_buf[1] = 0;
				ata_lbahigh_buf[0] = ata_lbahigh_buf[1] = 0;
				
			}else if( command == CMD_READ_DMA || command == CMD_WRITE_DMA){
				u8 t3, t2, t1, t0, count;
				t3 = inb(ATA_DRIVE_SELECT(ATA_BUS_PRIMARY)) & (u8)0x0F;
				t2 = inb(ATA_LBAHIGH(ATA_BUS_PRIMARY));
				t1 = inb(ATA_LBAMID(ATA_BUS_PRIMARY));
				t0 = inb(ATA_LBALOW(ATA_BUS_PRIMARY));
				count = inb(ATA_SECTOR_COUNT(ATA_BUS_PRIMARY));
				
				lba28addr = LBA28_TO_CPU32(t3, t2, t1, t0);

				//[DBG]
				printf("\nATA R/W DMA: 0x%02x (count=%02x, lba=%u", 
				command, count, lba28addr);
				
				//check if LBA is out of bounds
				if(check_if_LBA_outofbounds((u64)lba28addr)){
					printf("\nATA R/W DMA (OOB): 0x%02x (count=%02x, lba=(%02x%02x%02x%02x)", 
					command, count, t3, t2, t1, t0);
					//convert the access to a "null" sector
					CPU32_TO_LBA28((u32)LDN_NULL_SECTOR, &t3, &t2, &t1, &t0);

				//resend the new LBA and sector count addresses
				temp = inb(ATA_DRIVE_SELECT(ATA_BUS_PRIMARY)) & (u8)0xF0;
				temp |= t3;
				outb(temp, ATA_DRIVE_SELECT(ATA_BUS_PRIMARY));
				outb(count, ATA_SECTOR_COUNT(ATA_BUS_PRIMARY));
				outb(t2, ATA_LBAHIGH(ATA_BUS_PRIMARY));
				outb(t1, ATA_LBAMID(ATA_BUS_PRIMARY));
				outb(t0, ATA_LBALOW(ATA_BUS_PRIMARY));

				}
			
				
				ata_sector_count_index=0;
				ata_lbalow_index = ata_lbamid_index = ata_lbahigh_index=0;
				ata_sector_count_buf[0] = ata_sector_count_buf[1] = 0;
				ata_lbalow_buf[0] = ata_lbalow_buf[1] = 0;
				ata_lbamid_buf[0] = ata_lbamid_buf[1] = 0;
				ata_lbahigh_buf[0] = ata_lbahigh_buf[1] = 0;
				
			}else {
				printf("\nATA command: 0x%02x",	command);
			}
			
			ata_sector_count_index=0;
			ata_lbalow_index = ata_lbamid_index = ata_lbahigh_index=0;
			ata_sector_count_buf[0] = ata_sector_count_buf[1] = 0;
			ata_lbalow_buf[0] = ata_lbalow_buf[1] = 0;
			ata_lbamid_buf[0] = ata_lbamid_buf[1] = 0;
			ata_lbahigh_buf[0] = ata_lbahigh_buf[1] = 0;
			return APP_IOINTERCEPT_CHAIN;

	}
	
	return APP_IOINTERCEPT_CHAIN;	
}

