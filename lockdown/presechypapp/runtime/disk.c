//disk.c - low level PATA PIO routines
//author: amit vasudevan (amitvasudevan@acm.org)

#include <types.h>
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <machine.h>
#include <error.h>
#include <disk.h>

//---disk I/O
#define PORT_COMMAND	0x1F7
#define PORT_DRV			0x1F6
#define PORT_LBAHI		0x1F5
#define PORT_LBAMID		0x1F4
#define PORT_LBALOW		0x1F3
#define PORT_SECTOR		0x1F2
#define PORT_WRITE		0x1F1
#define PORT_READ			0x1F0


#define ATA_DEVICECONTROLREGISTER		0x3F6

#define ATA_STATUS_BSY	((u8)1 << 7)
#define ATA_STATUS_RDY  ((u8)1 << 6)
#define ATA_STATUS_DRQ	((u8)1 << 3)
#define ATA_STATUS_ERR	((u8)1 << 0)
#define ATA_STATUS_DF		((u8)1 << 5)

void ata_resetdrives(void){
	u8 status;
	
	outb(0x04, ATA_DEVICECONTROLREGISTER); 	//do a software reset on the bus
	outb(0x00, ATA_DEVICECONTROLREGISTER);	//reset bus to normal operation
	inb(ATA_DEVICECONTROLREGISTER);
	inb(ATA_DEVICECONTROLREGISTER);
	inb(ATA_DEVICECONTROLREGISTER);
	inb(ATA_DEVICECONTROLREGISTER);					//may take upto 4 tries for status
	
	status=inb(ATA_DEVICECONTROLREGISTER);
	while( !(!(status & ATA_STATUS_BSY) && (status & ATA_STATUS_RDY)) )
		status=inb(ATA_DEVICECONTROLREGISTER);
}

void udelay(u64 count){
	if (count)
		while (count --);
}

void DiskCopy(u32 srcdrive, u32 destdrive, u32 startsector, u32 endsector){
	u8 buffer[512];
	u32 i, status;
	
	printf("\nDiskCopy: srcdrive=0x%08X, destdrive=0x%08X, startsector=%u, endsector=%u",
			srcdrive, destdrive, startsector, endsector);
			
	for(i=startsector; i <= endsector; i++){
		if(!DiskReadSector(srcdrive, i, 1, &buffer)){
			printf("\nread error on sector %u", i);
			HALT();
		}
		if(!DiskWriteSector(destdrive, i, 1, &buffer)){
			printf("\nwrite error on sector %u", i);
			HALT();
		}
		if( (i % 10000) == 0 )
			printf("\nDone until %u (target=%u)", i, endsector);
	}
}

//returns 1 on success, 0 on failure
u32 DiskSetIndicator(u32 drive, u8 indicator){
	u8 buf[512];
	
	if(!DiskReadSector(drive, 0, 1, &buf))
		return 0;

	buf[444]= indicator;

	if(!DiskWriteSector(drive, 0, 1, &buf))
		return 0;
		
	return 1;
}

//returns 1 on success, 0 on failure
u32 DiskGetIndicator(u32 drive, u8 *indicatoraddr){
	u8 buf[512];
	
	if(!DiskReadSector(drive, 0, 1, &buf))
		return 0;
	
	*indicatoraddr = buf[444];
	return 1;
}

//return 1 on success, 0 on failure
u32 DiskReadSector(u32 drivenumber, u32 startsector, u8 sectorcount, u8 *buffer){
	u32 i;
	u16 tmp;
	u8 status;
	
	//1. select drive
	outb(0xE0 | (drivenumber << 4) | ((startsector >> 24) & 0x0F), 0x1F6);
	//2. send NULL
	outb(0x00, 0x1F1);
	//3. send sector count
	outb(sectorcount, 0x1F2);
	//4. bits 0-7 of lba
	outb(startsector, 0x1F3);
	//5. bits 8-15 of lba
	outb((startsector >> 8), 0x1F4); 
	//6. bits 16-23 of lba
	outb((startsector >> 16), 0x1F5);
	//7. send READ SECTOR command
	outb(0x20, 0x1F7);
	
	//8. read status, ignore it for 4 times
	inb(0x1F7);
	inb(0x1F7);
	inb(0x1F7);
	inb(0x1F7);
	
	//	
	//do{
	//	status = inb(0x1F7);
	//}while( !(!(status & ATA_STATUS_BSY) && (status & ATA_STATUS_DRQ) || (status & ATA_STATUS_ERR) || (status & ATA_STATUS_DF)) );
	
	//do{
		status = inb(0x1F7);
	//}while( !(!(status & ATA_STATUS_BSY) && (status & ATA_STATUS_DRQ) || (status & ATA_STATUS_ERR) || (status & ATA_STATUS_DF)) );
	
	
	if( (status & ATA_STATUS_ERR) || (status & ATA_STATUS_DF) )
		return 0;
	
	for (i = 0; i < sectorcount * 256; i++){
		tmp = inw(0x1F0);
		buffer[i*2] = (u8)tmp;
		buffer[(i*2)+1] = (u8)(tmp >> 8);
	}
}

u32 DiskWriteSector(u32 drivenumber, u32 startsector, u8 sectorcount, u8 *buffer){
	u32 i;
	u16 tmp;
	u8 status;
	
	//1. select drive
	outb(0xE0 | (drivenumber << 4) | ((startsector >> 24) & 0x0F), 0x1F6);
	//2. send NULL
	outb(0x00, 0x1F1);
	//3. send sector count
	outb(sectorcount, 0x1F2);
	//4. bits 0-7 of lba
	outb(startsector, 0x1F3);
	//5. bits 8-15 of lba
	outb((startsector >> 8), 0x1F4); 
	//6. bits 16-23 of lba
	outb((startsector >> 16), 0x1F5);
	//7. send WRITE SECTOR command
	outb(0x30, 0x1F7);
	
	//8. read status, ignore it for 4 times
	inb(0x1F7);
	inb(0x1F7);
	inb(0x1F7);
	inb(0x1F7);
	
	//	
	//while(1){
		status = inb(0x1F7);
	
	/*	if( (status & ATA_STATUS_ERR) || (status & ATA_STATUS_DF) )
			return 0;
		
		if( !(status & ATA_STATUS_BSY) && (status & ATA_STATUS_DRQ) )
			break;
	}	*/
	
	for (i = 0; i < sectorcount * 256; i++){
		tmp = buffer[i*2] | (buffer[(i*2)+ 1] << 8);
 		outw(tmp, 0x1F0);
	}

	//flush cache
	outb(0xE7, 0x1F7);
	inb(0x1F7);
	inb(0x1F7);
	inb(0x1F7);
	inb(0x1F7);

	while(1){
		status = inb(0x1F7);
	
		if( (status & ATA_STATUS_ERR) || (status & ATA_STATUS_DF) )
			return 0;
		
		if( !(status & ATA_STATUS_BSY) && (status & ATA_STATUS_RDY) )
			break;
	}	
	
	return 1;	
}

