/*
	BCM2837 (pi3) specific functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

void bcm2837_platform_initialize(void){
}


/*
	armlocalregisters_mailboxwrite_t *armlocalregisters_mailboxwrite;

	//map armlocalregisters_mailboxwrite
	armlocalregisters_mailboxwrite = (armlocalregisters_mailboxwrite_t *)(ARMLOCALREGISTERS_MAILBOXWRITE_BASE + (cpuid * sizeof(armlocalregisters_mailboxwrite_t)));

	_XDPRINTFSMP_("%s[%u]: armlocalregisters_mailboxwrite at 0x%08x\n", __func__, cpuid, armlocalregisters_mailboxwrite);

 */
