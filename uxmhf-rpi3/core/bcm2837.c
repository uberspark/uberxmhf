/*
	BCM2837 (pi3) specific functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

 __attribute__((section(".data"))) armlocalregisters_mailboxwrite_t *armlocalregisters_mailboxwrite[BCM2837_MAXCPUS];

void bcm2837_platform_initialize(void){
	//map armlocalregisters_mailboxwrite
	armlocalregisters_mailboxwrite = (armlocalregisters_mailboxwrite_t *[BCM2837_MAXCPUS])ARMLOCALREGISTERS_MAILBOXWRITE_BASE;

	_XDPRINTF_("%s: armlocalregisters_mailboxwrite at 0x%08x\n", __func__, armlocalregisters_mailboxwrite);
	_XDPRINTF_("%s: armlocalregisters_mailboxwrite[0] at 0x%08x\n", __func__, &armlocalregisters_mailboxwrite[0]);
	_XDPRINTF_("%s: armlocalregisters_mailboxwrite[1] at 0x%08x\n", __func__, &armlocalregisters_mailboxwrite[1]);
}
