//
//  $Id: uartISR.h 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/uart/uartISR.h $
//

#ifndef _UARTISR_H_
#define _UARTISR_H_

#include "FreeRTOS.h"
#include "queue.h"

//
//
//
void uartISRCreateQueues (portCHAR pxPort, unsigned portBASE_TYPE uxQueueLength, xQueueHandle *pxRX0Queue, xQueueHandle *pxTX0Queue, portLONG volatile **pplTHREEmptyFlag);
void uartISR0 (void);
void uartISR1 (void);
signed portBASE_TYPE uart0PostSpecialFromISR (U8 special);
signed portBASE_TYPE uart1PostSpecialFromISR (U8 special);

#endif
