/*
	watchdog hypapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

void uapp_watchdog_timerhandler(void){
	bcm2837_miniuart_puts("WATCHDOG EXCEPTION-- Resuming\n");
}
