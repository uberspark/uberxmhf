//
//  $Id: uartISR.c 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/uart/uartISR.c $
//

//
//  Standard includes
//
#include <stdlib.h>

//
//  Scheduler includes
//
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

//
//  Demo application includes
//
#include "uart.h"
#include "uartISR.h"

//
//  Constants to determine the ISR source
//
#define serSOURCE_THRE					  ((unsigned portCHAR) 0x02)
#define serSOURCE_RX_TIMEOUT			((unsigned portCHAR) 0x0c)
#define serSOURCE_ERROR					  ((unsigned portCHAR) 0x06)
#define serSOURCE_RX					    ((unsigned portCHAR) 0x04)
#define serINTERRUPT_SOURCE_MASK	((unsigned portCHAR) 0x0f)

//
//  Queues used to hold received characters, and characters waiting to be transmitted
//
static xQueueHandle xRX0Queue; 
static xQueueHandle xTX0Queue; 
static volatile portLONG lTHREEmpty0;
static xQueueHandle xRX1Queue; 
static xQueueHandle xTX1Queue; 
static volatile portLONG lTHREEmpty1;

//
//
//
void uartISRCreateQueues (portCHAR pxPort, unsigned portBASE_TYPE uxQueueLength, xQueueHandle *pxRX0Queue, xQueueHandle *pxTX0Queue, portLONG volatile **pplTHREEmptyFlag)
{
  switch (pxPort)
  {
    case 0:    
      {
        //
        //  Create the queues used to hold Rx and Tx characters
        //
        *pxRX0Queue = xRX0Queue = xQueueCreate (uxQueueLength, (unsigned portBASE_TYPE) sizeof (signed portCHAR));
        *pxTX0Queue = xTX0Queue = xQueueCreate (uxQueueLength + 1, (unsigned portBASE_TYPE) sizeof (signed portCHAR));

        //
        //  Initialise the THRE empty flag - and pass back a reference
        //
        lTHREEmpty0 = (portLONG) pdTRUE;
        *pplTHREEmptyFlag = &lTHREEmpty0;
      }
      break;

    case 1:
      {
        //
        //  Create the queues used to hold Rx and Tx characters
        //
        *pxRX0Queue = xRX1Queue = xQueueCreate (uxQueueLength, (unsigned portCHAR) sizeof (signed portCHAR));
        *pxTX0Queue = xTX1Queue = xQueueCreate (uxQueueLength + 1, (unsigned portCHAR) sizeof (signed portCHAR));

        //
        //  Initialise the THRE empty flag - and pass back a reference
        //
        lTHREEmpty1 = (portLONG) pdTRUE;
        *pplTHREEmptyFlag = &lTHREEmpty1;	
      }
      break;
  }
}

//
//
//
static void uartISR0_Handler (void)
{
  signed portCHAR cChar;
  portBASE_TYPE higherPriorityTaskWoken = pdFALSE;

  switch (UART0_IIR & serINTERRUPT_SOURCE_MASK)
  {
    //
    //  Not handling this, but clear the interrupt
    //
    case serSOURCE_ERROR :	
      {
        cChar = UART0_LSR;
      }
      break;

    //
    //  The THRE is empty.  If there is another character in the Tx queue, send it now,
    //  otherwise, no more characters, so indicate THRE is available
    //
    case serSOURCE_THRE	:	
      {
        if (xQueueReceiveFromISR (xTX0Queue, &cChar, &higherPriorityTaskWoken) == pdPASS)
          UART0_THR = cChar;
        else
          lTHREEmpty0 = pdTRUE;
      }
      break;

    //
    //  A character was received.  Place it in the queue of received characters
    //
    case serSOURCE_RX_TIMEOUT :
    case serSOURCE_RX	:	
      {
        cChar = UART0_RBR;

        xQueueSendFromISR (xRX0Queue, &cChar, &higherPriorityTaskWoken);
      }
      break;

    default	:
      break;
  }

  VIC_VectAddr = (unsigned portLONG) 0;

  if (higherPriorityTaskWoken)
    portYIELD_FROM_ISR ();
}

void uartISR0 (void) __attribute__ ((naked));
void uartISR0 (void)
{
  portSAVE_CONTEXT ();
  uartISR0_Handler ();
  portRESTORE_CONTEXT ();
}

//
//
//
static void uartISR1_Handler (void)
{
  signed portCHAR cChar;
  portBASE_TYPE higherPriorityTaskWoken = pdFALSE;

  switch (UART1_IIR & serINTERRUPT_SOURCE_MASK)
  {
    //
    //  Not handling this, but clear the interrupt
    //
    case serSOURCE_ERROR :
      {
        cChar = UART1_LSR;
      }
      break;

    //
    //  The THRE is empty.  If there is another character in the Tx queue, send it now,
    //  otherwise, no more characters, so indicate THRE is available
    //
    case serSOURCE_THRE	:
      {
        if (xQueueReceiveFromISR (xTX1Queue, &cChar, &higherPriorityTaskWoken) == pdPASS)
          UART1_THR = cChar;
        else
          lTHREEmpty1 = pdTRUE;
      }
      break;

    //
    //  A character was received.  Place it in the queue of received characters
    //
    case serSOURCE_RX_TIMEOUT :
    case serSOURCE_RX	:
      {
        cChar = UART1_RBR;

        xQueueSendFromISR (xRX1Queue, &cChar, &higherPriorityTaskWoken);
      }
      break;

    default	:
      break;
  }

  VIC_VectAddr = (unsigned portLONG) 0;

  if (higherPriorityTaskWoken)
    portYIELD_FROM_ISR ();
}

void uartISR1 (void) __attribute__ ((naked));
void uartISR1 (void)
{
  portSAVE_CONTEXT ();
  uartISR1_Handler ();
  portRESTORE_CONTEXT ();
}
