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


void bcm2837_platform_smpinitialize(void){
	u32 i;
	armlocalregisters_mailboxwrite_t *armlocalregisters_mailboxwrite;

	_XDPRINTFSMP_("%s: cpu 0: boot processor\n", __func__);

	for(i=1; i < BCM2837_MAXCPUS; i++){
		//map armlocalregisters_mailboxwrite
		armlocalregisters_mailboxwrite = (armlocalregisters_mailboxwrite_t *)(ARMLOCALREGISTERS_MAILBOXWRITE_BASE + (i * sizeof(armlocalregisters_mailboxwrite_t)));

		_XDPRINTFSMP_("%s: cpu %u: armlocalregisters_mailboxwrite at 0x%08x\n", __func__, i, armlocalregisters_mailboxwrite);
		_XDPRINTFSMP_("%s: cpu %u: armlocalregisters_mailboxwrite->mailbox3write at 0x%08x\n", __func__, i, &armlocalregisters_mailboxwrite->mailbox3write);
	}

}
