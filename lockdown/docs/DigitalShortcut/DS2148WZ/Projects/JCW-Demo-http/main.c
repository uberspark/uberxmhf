//
//  $Id: main.c 77 2008-10-06 00:57:05Z jcw $
//  $Revision: 77 $
//  $Author: jcw $
//  $Date: 2008-10-05 20:57:05 -0400 (Sun, 05 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/main.c $
//	Small changes by Digital Shortcut Inc. - JD 10/12/2008

//
//  Standard includes
//
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

//
// Scheduler includes
//
#include "FreeRTOS.h"
#include "task.h"

//
//  Demo application includes
//
#include "main.h"
#include "cpu/cpu.h"
#include "digi_short/toggle.h"
#include "digi_short/wiz_ds.h"
#include "eints/eints.h"
#include "fiq/fiq.h"
#include "i2c/i2c.h"
#include "leds/leds.h"
#include "monitor/monitor.h"
#include "timer/timer.h"
#include "uart/uart.h"
#include "usbser/usbser.h"
#include "digi_short/httpserv.h"

#define BAUD_UART0 115200

unsigned int	VoltVal;
extern	uint8		phpBuf[];

portTASK_FUNCTION (vUpdateVoltTask, pvParameters __attribute__ ((unused)));


xTaskHandle taskHandles [TASKHANDLE_LAST];

// Pseudo AD_Voltage Converter
portTASK_FUNCTION (vUpdateVoltTask, pvParameters __attribute__ ((unused)))
{
	int v;
	char tb[10];
	
	for (;;)  {
		VoltVal++;
		v = 200+(VoltVal%120); // miliVolts in range 200-319
	
		itoa(v, tb, 10);
		memcpy ( (char*)&phpBuf[2], &tb[3], 3);
		
		taskYIELD();
	}
}


int main (void)
{
  cpuSetupHardware ();
  uartInit (0, BAUD_UART0, 64);
  
  usbserInit ();
  timerInit ();
  i2cInit ();
  eintsInit ();
  fiqInit ();
  
  w5300Init();		// Digital Shortcut - Init for Http Server

  memset (taskHandles, 0, sizeof (taskHandles));

  xTaskCreate (vMonitorTask,  (const signed portCHAR * const) "Monitor",  1024,                     NULL, (tskIDLE_PRIORITY + 3), &taskHandles [TASKHANDLE_MONITOR]);
  xTaskCreate (vLEDFlashTask, (const signed portCHAR * const) "LEDx",     configMINIMAL_STACK_SIZE, NULL, (tskIDLE_PRIORITY + 2), &taskHandles [TASKHANDLE_LED]);
  xTaskCreate (vPinToggleTask, (const signed portCHAR * const) "ToggleP0.6", configMINIMAL_STACK_SIZE, NULL, (tskIDLE_PRIORITY + 1), &taskHandles [TASKHANDLE_TOGGLE]);
  xTaskCreate (vUpdateVoltTask, (const signed portCHAR * const) "UpdateVolt", configMINIMAL_STACK_SIZE, NULL, (tskIDLE_PRIORITY + 1), &taskHandles [TASKHANDLE_UPDATEV]);
  xTaskCreate (vHttpServTask, (const signed portCHAR * const) "HttpServr", configMINIMAL_STACK_SIZE, NULL, (tskIDLE_PRIORITY + 1), &taskHandles [TASKHANDLE_HTTPSERV]);

  vTaskStartScheduler ();

  return 0;
}
