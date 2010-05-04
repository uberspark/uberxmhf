//
//  $Id: uart.c 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/uart/uart.c $
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
//  Constants to setup and access the UART
//
#define serWANTED_CLOCK_SCALING	  ((unsigned portLONG) 16)

//
//  Constants to setup and access the VIC
//
#define serINVALID_QUEUE				  ((xQueueHandle) 0)
#define serHANDLE					        ((xComPortHandle) 1)
#define serNO_BLOCK					      ((portTickType) 0)

//
//  Queues used to hold received characters, and characters waiting to be transmitted
//
static xQueueHandle xRX0Queue; 
static xQueueHandle xTX0Queue; 
static xQueueHandle xRX1Queue; 
static xQueueHandle xTX1Queue; 

//
//  Communication flag between the interrupt service routine and serial API
//
static volatile portLONG *plTHREEmpty;
static volatile portLONG *plTHREEmpty1;

//
//
//
xComPortHandle uartInit (portCHAR pxPort, unsigned portLONG ulWantedBaud, unsigned portBASE_TYPE uxQueueLength)
{
  unsigned portLONG ulDivisor;
  unsigned portLONG ulWantedClock;
  xComPortHandle xReturn = serHANDLE;

  switch (pxPort)
  {
    case 0 :    
      {
        uartISRCreateQueues (0, uxQueueLength, &xRX0Queue, &xTX0Queue, &plTHREEmpty);

        if ((xRX0Queue != serINVALID_QUEUE) && 
            (xTX0Queue != serINVALID_QUEUE) && 
            (ulWantedBaud != (unsigned portLONG) 0) 
           )
        {
          portENTER_CRITICAL ();

          {
            SCB_PCONP |= SCB_PCONP_PCUART0;

            //
            //  Setup the baud rate:  Calculate the divisor value
            //
            ulWantedClock = ulWantedBaud * serWANTED_CLOCK_SCALING;
            ulDivisor = configCPU_CLOCK_HZ / ulWantedClock;

            //
            //  Set the DLAB bit so we can access the divisor
            //
            UART0_LCR |= UART_LCR_DLAB;

            //
            //  Setup the divisor
            //
            UART0_DLL = (unsigned portCHAR) (ulDivisor & (unsigned portLONG) 0xff);
            ulDivisor >>= 8;
            UART0_DLM = (unsigned portCHAR) (ulDivisor & (unsigned portLONG) 0xff);

            //
            //  Turn on the FIFO's and clear the buffers
            //
            UART0_FCR = UART_FCR_EN | UART_FCR_CLR;

            //
            //  Setup transmission format
            //
            UART0_LCR = UART_LCR_NOPAR | UART_LCR_1STOP | UART_LCR_8BITS;

            //
            //  Setup the VIC for the UART
            //
            VIC_IntSelect &= ~VIC_IntSelect_UART0;
            VIC_VectAddr2 = (portLONG) uartISR0;
            VIC_VectCntl2 = VIC_VectCntl_ENABLE | VIC_Channel_UART0;
            VIC_IntEnable = VIC_IntEnable_UART0;

            //
            //  Enable UART0 interrupts
            //
            UART0_IER |= UART_IER_EI;
          }

          portEXIT_CRITICAL ();
        }
        else
          xReturn = (xComPortHandle) 0;
      }
      break;

    case 1:
      {
        uartISRCreateQueues (1, uxQueueLength, &xRX1Queue, &xTX1Queue, &plTHREEmpty1);

        if ((xRX1Queue != serINVALID_QUEUE) && 
            (xTX1Queue != serINVALID_QUEUE) && 
            (ulWantedBaud != (unsigned portLONG) 0) 
           )
        {
          portENTER_CRITICAL ();

          {
            SCB_PCONP |= SCB_PCONP_PCUART1;

            //
            //  Setup the baud rate:  Calculate the divisor value
            //
            ulWantedClock = ulWantedBaud * serWANTED_CLOCK_SCALING;
            ulDivisor = configCPU_CLOCK_HZ / ulWantedClock;

            //
            //  Set the DLAB bit so we can access the divisor
            //
            UART1_LCR |= UART_LCR_DLAB;

            //
            //  Setup the divisor
            //
            UART1_DLL = (unsigned portCHAR) (ulDivisor & (unsigned portLONG) 0xff);
            ulDivisor >>= 8;
            UART1_DLM = (unsigned portCHAR) (ulDivisor & (unsigned portLONG) 0xff);

            //
            //  Turn on the FIFO's and clear the buffers
            //
            UART1_FCR = UART_FCR_EN | UART_FCR_CLR;

            //
            //  Setup transmission format
            //
            UART1_LCR = UART_LCR_NOPAR | UART_LCR_1STOP | UART_LCR_8BITS;

            //
            //  Setup the VIC for the UART
            //
            VIC_IntSelect &= ~VIC_IntSelect_UART1;
            VIC_VectAddr3 = (portLONG) uartISR1;
            VIC_VectCntl3 = VIC_VectCntl_ENABLE | VIC_Channel_UART1;
            VIC_IntEnable = VIC_IntEnable_UART1;

            //
            //  Enable UART0 interrupts//
            //
            UART1_IER |= UART_IER_EI;
          }

          portEXIT_CRITICAL ();
        }
        else
          xReturn = (xComPortHandle) 0;
      }
      break;
  }

  return xReturn;
}

signed portBASE_TYPE uartGetChar (portCHAR pxPort, signed portCHAR *pcRxedChar, portTickType xBlockTime)
{
  switch (pxPort)
  {
    //
    //  Get the next character from the buffer.  Return false if no characters are available, or arrive before xBlockTime expires
    //
    case 0:    
      {
        if (xQueueReceive (xRX0Queue, pcRxedChar, xBlockTime))
          return pdTRUE;
        else
          return pdFALSE;
      }
      break;

      //
      //  Get the next character from the buffer.  Return false if no characters are available, or arrive before xBlockTime expires
      //
    case 1:
      {
        if (xQueueReceive (xRX1Queue, pcRxedChar, xBlockTime))
          return pdTRUE;
        else
          return pdFALSE;
      }
      break;
  }

  return pdFALSE;
}

//
//
//
void uartPutString (portCHAR pxPort, const signed portCHAR * const pcString, portTickType xBlockTime)
{
  signed portCHAR *pxNext;

  pxNext = (signed portCHAR *) pcString;

  while (*pxNext)
  {
    uartPutChar (pxPort, *pxNext, xBlockTime);
    pxNext++;
  }
}

//
//
//
signed portBASE_TYPE uartPutChar (portCHAR pxPort, signed portCHAR cOutChar, portTickType xBlockTime)
{
  signed portBASE_TYPE xReturn = 0;

  switch (pxPort)
  {
    case 0 :    
      {
        portENTER_CRITICAL ();

        {
          //
          //  Is there space to write directly to the UART?
          //
          if (*plTHREEmpty == (portLONG) pdTRUE)
          {
            *plTHREEmpty = pdFALSE;
            UART0_THR = cOutChar;
            xReturn = pdPASS;
          }
          else 
          {
            //
            //  We cannot write directly to the UART, so queue the character.  Block for a maximum of 
            //  xBlockTime if there is no space in the queue.
            //
            xReturn = xQueueSend (xTX0Queue, &cOutChar, xBlockTime);

            //
            //  Depending on queue sizing and task prioritisation:  While we were blocked waiting to post 
            //  interrupts were not disabled.  It is possible that the serial ISR has emptied the Tx queue, 
            //  in which case we need to start the Tx off again.
            //
            if ((*plTHREEmpty == (portLONG) pdTRUE) && (xReturn == pdPASS))
            {
              xQueueReceive (xTX0Queue, &cOutChar, serNO_BLOCK);
              *plTHREEmpty = pdFALSE;
              UART0_THR = cOutChar;
            }
          }
        }

        portEXIT_CRITICAL ();
      }
      break;

    case 1 :
      {
        portENTER_CRITICAL ();

        {
          //
          //  Is there space to write directly to the UART?
          //
          if (*plTHREEmpty1 == (portLONG) pdTRUE)
          {
            *plTHREEmpty1 = pdFALSE;
            UART1_THR = cOutChar;
            xReturn = pdPASS;
          }
          else 
          {
            //
            //  We cannot write directly to the UART, so queue the character.  Block for a maximum of 
            //  xBlockTime if there is no space in the queue.
            //
            xReturn = xQueueSend (xTX1Queue, &cOutChar, xBlockTime);

            //
            //  Depending on queue sizing and task prioritisation:  While we were blocked waiting to post 
            //  interrupts were not disabled.  It is possible that the serial ISR has emptied the Tx queue, 
            //  in which case we need to start the Tx off again.
            //
            if ((*plTHREEmpty1 == (portLONG) pdTRUE) && (xReturn == pdPASS))
            {
              xQueueReceive (xTX1Queue, &cOutChar, serNO_BLOCK);
              *plTHREEmpty1 = pdFALSE;
              UART1_THR = cOutChar;
            }
          }
        }

        portEXIT_CRITICAL ();	
      }
      break;

    default:
      return xReturn;
      break;
  }

  return xReturn;
}

//
//
//
void uart0GetRxQueue (xQueueHandle *qh)
{
  *qh = xRX0Queue;
}

void uart1GetRxQueue (xQueueHandle *qh)
{
  *qh = xRX1Queue;
}
