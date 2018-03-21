/*
	watchdog hypapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>


__attribute__((section(".data"))) volatile u32 *gpio;
bool led_on=false;

#define INP_GPIO(g) *(gpio+((g)/10)) &= ~(7<<(((g)%10)*3))
#define OUT_GPIO(g) *(gpio+((g)/10)) |=  (1<<(((g)%10)*3))
#define GPIO_SET *(gpio+7)  // sets   bits which are 1 ignores bits which are 0
#define GPIO_CLR *(gpio+10) // clears bits which are 1 ignores bits which are 0

void uapp_watchdog_timerhandler(void){
	gpio = (u32 *)GPIO_BASE;

	// set GPIO pin 7 as output
	INP_GPIO(7); // must use INP_GPIO before we can use OUT_GPIO
	OUT_GPIO(7);

	if(led_on){
		GPIO_CLR = (1 << 7);
		led_on=false;
	}else{
		GPIO_SET = (1 << 7);
		led_on=true;
	}

	//bcm2837_miniuart_puts("WATCHDOG EXCEPTION-- Resuming\n");
}
