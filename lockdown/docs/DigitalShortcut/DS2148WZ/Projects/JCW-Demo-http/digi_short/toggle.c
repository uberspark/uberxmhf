/** file toggle.c
 * DS2148WZ Pin Toggle Tasks
 *
 * Rev 1.0 JD 1-07-2009
 * Copyright Digital Shortcut Inc. (BSD licence) 2009 **/

#include "FreeRTOS.h"
#include "task.h"

#include "toggle.h"

extern	void	delay(unsigned long d);
extern	signed portBASE_TYPE uartPutChar (portCHAR pxPort, signed portCHAR cOutChar, portTickType xBlockTime);

// Pin P0.6 (Header P3-18) Toggle Task
portTASK_FUNCTION (vPinToggleTask, pvParameters __attribute__ ((unused)))
{
	for (;;)  {
		if (GPIO0_FIOPIN & GPIO_IO_P6) 
			GPIO0_FIOCLR = GPIO_IO_P6;
		else GPIO0_FIOSET = GPIO_IO_P6;

		taskYIELD();
	}
}

// Pin P0.7 (Header P3-17) Toggle Task
portTASK_FUNCTION (vPinToggDelTask, pvParameters __attribute__ ((unused)))
{
	for (;;)  {
		if (GPIO0_FIOPIN & GPIO_IO_P7) 
			GPIO0_FIOCLR = GPIO_IO_P7;
		else GPIO0_FIOSET = GPIO_IO_P7;
		
		delay(200000);				// wait 20msec 
		//delay(100);				

		taskYIELD();
	}
}

// Pin P0.12 (Header P2-28) Toggle Task
portTASK_FUNCTION (vPinSlowTask, pvParameters __attribute__ ((unused)))
{
  portTickType lastTickTime;
  
	lastTickTime = xTaskGetTickCount ();

	for (;;)  {
    vTaskDelayUntil (&lastTickTime, 5);
    GPIO0_FIOSET = GPIO_IO_P12;
    vTaskDelayUntil (&lastTickTime, 5);
    GPIO0_FIOCLR = GPIO_IO_P12;
	}
}

