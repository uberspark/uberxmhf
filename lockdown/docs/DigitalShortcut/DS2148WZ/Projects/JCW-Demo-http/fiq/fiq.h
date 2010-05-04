//
//  $Id: fiq.h 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/fiq/fiq.h $
//

#ifndef _FIQ_H_
#define _FIQ_H_

void fiqInit (void);
int fiqEnable (void);
int fiqDisable (void);
unsigned int fiqGetCount (void);
void fiqClearCount (void);
void fiqISR (void);
unsigned char *fiqFIQISRCopyToRAM (void);

#endif
