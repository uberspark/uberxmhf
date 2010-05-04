//------------------------------------------------------------------------------
// hp_sdisk_ata.c
// hyper-partitioning implementation for multiple partitions on a single
// ata disk
// author: amit vasudevan (amitvasudevan@acm.org) 

#include <types.h>
#include <print.h>
#include <msr.h>
#include <processor.h>
//#include <svm.h>
#include <paging.h>
#include <io.h>
#include <target.h>
#include <vtx.h>
#include <machine.h>

#include <ata-atapi.h>

extern struct vmcb_struct *win_vmcb;
extern u32 guest_RAX;

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


//check if a given LBA is out of bounds of the partition
//returns 1 if out of bounds, else 0
u32 check_if_LBA_outofbounds(u64 lbaaddr){
	if( (((u64)lbaaddr >= (u64)__GUESTOS_UNTRUSTED_BOOTPARTITION_STARTSECTOR)
			&& ((u64)lbaaddr <= (u64)__GUESTOS_UNTRUSTED_BOOTPARTITION_ENDSECTOR))
			|| ((u64)lbaaddr >= 0ULL && (u64)lbaaddr <= 63ULL) )
			return 0; //not out of bounds
	else
			return 1; //out of bounds
}


//returns IOIO_SKIP or IOIO_CHAIN
//u32 hp(ioio_info_t *ioinfo){
u32 hp(u32 portnum, u32 access_type, u32 access_size){
	u8 command, temp;
	u64 lba48addr;
	u32 lba28addr;
	
	if (access_size != IO_SIZE_BYTE){
		printf("\nNon-byte access to port unsupported. HALT!");
		HALT();
	}

	if(access_type == IO_TYPE_IN)	//IN, we simply chain
		return IOIO_CHAIN;

	//check for correct disk
	temp=inb(ATA_DRIVE_SELECT(ATA_BUS_PRIMARY));
	if(temp & 0x10)	//slave, so simply chain
		return IOIO_CHAIN;

	switch(portnum){
		case ATA_SECTOR_COUNT(ATA_BUS_PRIMARY):
			if(ata_sector_count_index > 1){
				ata_sector_count_buf[0]=ata_sector_count_buf[1];
				ata_sector_count_buf[1]=(u8)guest_RAX;
			}else{
				ata_sector_count_buf[ata_sector_count_index]=(u8)guest_RAX;
			}
			ata_sector_count_index++;
			return(IOIO_CHAIN);
		
		case ATA_LBALOW(ATA_BUS_PRIMARY):
			if(ata_lbalow_index > 1){
				ata_lbalow_buf[0]=ata_lbalow_buf[1];
				ata_lbalow_buf[1]=(u8)guest_RAX;
			}else{
				ata_lbalow_buf[ata_lbalow_index]=(u8)guest_RAX;
			}
			ata_lbalow_index++;
			return(IOIO_CHAIN);
			
		case ATA_LBAMID(ATA_BUS_PRIMARY):
			if(ata_lbamid_index > 1){
				ata_lbamid_buf[0]=ata_lbamid_buf[1];
				ata_lbamid_buf[1]=(u8)guest_RAX;
			}else{
				ata_lbamid_buf[ata_lbamid_index]=(u8)guest_RAX;
			}
			ata_lbamid_index++;
			return(IOIO_CHAIN);

		case ATA_LBAHIGH(ATA_BUS_PRIMARY):
			if(ata_lbahigh_index > 1){
				ata_lbahigh_buf[0]=ata_lbahigh_buf[1];
				ata_lbahigh_buf[1]=(u8)guest_RAX;
			}else{
				ata_lbahigh_buf[ata_lbahigh_index]=(u8)guest_RAX;
			}
			ata_lbahigh_index++;
			return(IOIO_CHAIN);
	
		case ATA_COMMAND(ATA_BUS_PRIMARY):
			command = (u8)guest_RAX;
			if(command == CMD_READ_DMA_EXT || command == CMD_WRITE_DMA_EXT){
				lba48addr = LBA48_TO_CPU64(0x00, 0x00, ata_lbahigh_buf[0], 
					ata_lbamid_buf[0], ata_lbalow_buf[0], ata_lbahigh_buf[1], 
					ata_lbamid_buf[1], ata_lbalow_buf[1]);

				//[DBG]
				printf("\nATA R/W DMA EXT: 0x%02x (count=%02x%02x, lba=%02x%02x%02x%02x%02x%02x)", 
				command, ata_sector_count_buf[0], ata_sector_count_buf[1],
					ata_lbahigh_buf[0], ata_lbamid_buf[0], ata_lbalow_buf[0],
					ata_lbahigh_buf[1], ata_lbamid_buf[1], ata_lbalow_buf[1]);

				//check if we are out of bounds
				if(check_if_LBA_outofbounds(lba48addr)){
					printf("\nATA R/W DMA EXT: 0x%02x (count=%02x%02x, lba=%02x%02x%02x%02x%02x%02x)", 
						command, ata_sector_count_buf[0], ata_sector_count_buf[1],
						ata_lbahigh_buf[0], ata_lbamid_buf[0], ata_lbalow_buf[0],
						ata_lbahigh_buf[1], ata_lbamid_buf[1], ata_lbalow_buf[1]);
					//convert the access to the "null" sector	
					CPU64_TO_LBA48((u64)__GUESTOS_NULLSECTOR, &ata_lbahigh_buf[0], 
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
				printf("\nATA R/W DMA: 0x%02x (count=%02x, lba=(%02x%02x%02x%02x)", 
				command, count, t3, t2, t1, t0);
				
				//check if LBA is out of bounds
				if(check_if_LBA_outofbounds((u64)lba28addr)){
					printf("\nATA R/W DMA: 0x%02x (count=%02x, lba=(%02x%02x%02x%02x)", 
					command, count, t3, t2, t1, t0);
					//convert the access to a "null" sector
					CPU32_TO_LBA28((u32)__GUESTOS_NULLSECTOR, &t3, &t2, &t1, &t0);

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
			return IOIO_CHAIN;

	}
	
	return IOIO_CHAIN;	
}

//------------------------------------------------------------------------------
// obsolete, test code follows
/*
//lbatype = LBA28 or LBA48 or LBANONE on return
u64 maptrustedsector(u64 olbaaddr, u8 *lbatype){
	if(olbaaddr < (u64)__GUESTOS_UNTRUSTED_BOOTPARTITION_STARTSECTOR ||
		olbaaddr > (u64)__GUESTOS_UNTRUSTED_BOOTPARTITION_ENDSECTOR){
		printf("\nolbaaddr=0x%016llx not within bootpartition, skipping!",
			olbaaddr);
		*lbatype = LBANONE;
		return olbaaddr;	
	}

	olbaaddr = olbaaddr - (u64)__GUESTOS_UNTRUSTED_BOOTPARTITION_STARTSECTOR + (u64)__GUESTOS_TRUSTED_BOOTPARTITION_STARTSECTOR;

	if(olbaaddr > (u64)LBA28MAXSECTOR)
		*lbatype = LBA48;
	else
		*lbatype = LBA28;		
}

//lbatype = LBA28 or LBA48
void resendsectorrequest(u64 lbaaddr, u16 sectorcount, u8 lbatype){
	ASSERT( (lbatype == LBA28) || (lbatype == LBA48) );
	
	switch(lbatype){
		case LBA28:{
			u8 t3, t2, t1, t0, count, temp;
			CPU32_TO_LBA28((u32)lbaaddr, &t3, &t2, &t1, &t0);
			count = (u8)sectorcount;
			temp = inb(ATA_DRIVE_SELECT(ATA_BUS_PRIMARY)) & (u8)0xF0;
			temp |= t3;
			outb(temp, ATA_DRIVE_SELECT(ATA_BUS_PRIMARY));
			outb(count, ATA_SECTOR_COUNT(ATA_BUS_PRIMARY));
			outb(t2, ATA_LBAHIGH(ATA_BUS_PRIMARY));
			outb(t1, ATA_LBAMID(ATA_BUS_PRIMARY));
			outb(t0, ATA_LBALOW(ATA_BUS_PRIMARY));
		}
		break;
		
		case LBA48:{
			u8 t5, t4, t3, t2, t1, t0;
			CPU64_TO_LBA48(lbaaddr, &t5, &t4, &t3, &t2,	&t1, &t0);
			outb ((u8)sectorcount, ATA_SECTOR_COUNT(ATA_BUS_PRIMARY));
			outb (t3, ATA_LBALOW(ATA_BUS_PRIMARY));
			outb (t4, ATA_LBAMID(ATA_BUS_PRIMARY));
			outb (t5, ATA_LBAHIGH(ATA_BUS_PRIMARY));
			outb ( (u8) ((u16)sectorcount >> 8), ATA_SECTOR_COUNT(ATA_BUS_PRIMARY));
			outb (t0, ATA_LBALOW(ATA_BUS_PRIMARY));
			outb (t1, ATA_LBAMID(ATA_BUS_PRIMARY));
			outb (t2, ATA_LBAHIGH(ATA_BUS_PRIMARY));
		}
		break;
	}

}



*/

/*

			}else if(command == CMD_READ_MULTIPLE || command == CMD_WRITE_MULTIPLE
				|| command == CMD_READ_SECTORS || command == CMD_WRITE_SECTORS){
				u8 t3, t2, t1, t0, count;
				u8 finalcommand;
				
				t3 = inb(ATA_DRIVE_SELECT(ATA_BUS_PRIMARY)) & (u8)0x0F;
				t2 = inb(ATA_LBAHIGH(ATA_BUS_PRIMARY));
				t1 = inb(ATA_LBAMID(ATA_BUS_PRIMARY));
				t0 = inb(ATA_LBALOW(ATA_BUS_PRIMARY));
				count = inb(ATA_SECTOR_COUNT(ATA_BUS_PRIMARY));
				
				lba28addr = LBA28_TO_CPU32(t3, t2, t1, t0);
				
				//convert to LBA48 
				outb(0x40, ATA_DRIVE_SELECT(ATA_BUS_PRIMARY));
				resendsectorrequest((u64)lba28addr, 
						(u16) ( ((u16)ata_sector_count_buf[1] << 8) | (u16)ata_sector_count_buf[0] ),
						LBA48);
				
				if(command == CMD_READ_MULTIPLE)
					finalcommand = CMD_READ_MULTIPLE_EXT;
				else if(command == CMD_WRITE_MULTIPLE)
					finalcommand = CMD_WRITE_MULTIPLE_EXT;
				else if(command == CMD_READ_SECTORS)
					finalcommand = CMD_READ_SECTORS_EXT;
				else if(command == CMD_WRITE_SECTORS)
					finalcommand = CMD_WRITE_SECTORS_EXT;
				
				printf("\nChanged command 0x%02x to 0x%02x", command, finalcommand);
				outb(finalcommand, ATA_COMMAND(ATA_BUS_PRIMARY));
				
				ata_sector_count_index=0;
				ata_lbalow_index = ata_lbamid_index = ata_lbahigh_index=0;
				ata_sector_count_buf[0] = ata_sector_count_buf[1] = 0;
				ata_lbalow_buf[0] = ata_lbalow_buf[1] = 0;
				ata_lbamid_buf[0] = ata_lbamid_buf[1] = 0;
				ata_lbahigh_buf[0] = ata_lbahigh_buf[1] = 0;
				
				return(IOIO_SKIP);
				


*/