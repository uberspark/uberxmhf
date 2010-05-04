//
//  $Id: spi.h 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/mmc/spi.h $
//

#ifndef _MMCLLSPI1_H_
#define _MMCLLSPI1_H_

#include "sysdefs.h"

//
//  Hardware depends definitions
//
#define IDENTIFICATIONMODECLOCK   400000l
#define SYSTEMPERIPHERIALCLOCK  48000000l
#define SPI_DLY_1MSEC                1000

//
//
//
inline int spiHardwareCardPresent (void);
inline int spiHardwareWriteProtected (void);
void spiChipSelect (BOOL select);
inline BOOL spiPresent (void);
inline BOOL spiWriteProtect (void);
U32 spiSetClockFreq (U32 frequency);
void spiInit (void);
U8 spiTransferByte (U8 c);
U8 spiWaitReady (void);
void spiSendBlock (const U8 *pData, U32 size);
void spiReceiveBlock (U8 *pData, U32 size);
void spiDelay1ms (U32 delay);

#endif
