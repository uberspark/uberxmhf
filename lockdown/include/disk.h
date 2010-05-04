//author: amit vasudevan(amitvasudevan@acm.org)
#ifndef __DISK_H_
#define __DISK_H_



#ifndef __ASSEMBLY__
u32 DiskSetIndicator(u32 drive, u8 indicator);
u32 DiskGetIndicator(u32 drive, u8 *indicatoraddr);
u32 DiskReadSector(u32 drivenumber, u32 startsector, u8 sectorcount, u8 *buffer);
u32 DiskWriteSector(u32 drivenumber, u32 startsector, u8 sectorcount, u8 *buffer);

#endif /* __ASSEMBLY__ */

#endif /* __DISK_H_ */
