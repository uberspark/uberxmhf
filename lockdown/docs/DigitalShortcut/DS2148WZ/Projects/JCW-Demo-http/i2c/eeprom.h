//
//  $Id: eeprom.h 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/i2c/eeprom.h $
//

#ifndef _EEPROM_H_
#define _EEPROM_H_

//
//
//
#define EEPROM_ADDRESS  (0xa0)
#define EEPROM_SIZE     (131072)
#define EEPROM_PAGESIZE (256)

//
//
//
void eepromInit (void);
int eepromSetAddress (U32 address);
U32 eepromGetAddress (void);
int eepromRead (U8 *buffer, U32 bufferLength);
int eepromReadAddress (U32 address, U8 *buffer, U32 bufferLength);
int eepromWrite (U8 *buffer, U32 bufferLength);
int eepromWriteAddress (U32 address, U8 *buffer, U32 bufferLength);
int eepromFillAddress (U32 address, U32 length, U8 fillValue);

#endif
