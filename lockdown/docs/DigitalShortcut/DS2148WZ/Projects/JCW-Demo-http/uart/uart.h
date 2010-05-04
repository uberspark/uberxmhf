//
//  $Id: uart.h 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/uart/uart.h $
//

#ifndef _UART_H_
#define _UART_H_

#include "FreeRTOS.h"
#include "queue.h"

typedef void *xComPortHandle;

xComPortHandle uartInit (portCHAR pxPort, unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength);
void uartPutString (portCHAR pxPort, const signed portCHAR * const pcString, portTickType xBlockTime);
signed portBASE_TYPE uartGetChar (portCHAR pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime);
signed portBASE_TYPE uartPutChar (portCHAR pxPort, signed portCHAR cOutChar, portTickType xBlockTime);
void uartClose (portCHAR xPort);
void uart0GetRxQueue (xQueueHandle *qh);
void uart1GetRxQueue (xQueueHandle *qh);

#endif
