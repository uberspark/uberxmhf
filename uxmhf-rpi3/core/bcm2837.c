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
	armlocalregisters_mailboxwrite_t *armlocalregisters_mailboxwrite_cpu1;
	armlocalregisters_mailboxreadclear_t *armlocalregisters_mailboxreadclear_cpu1;

	_XDPRINTFSMP_("%s: cpu 0: boot processor\n", __func__);

	//map armlocalregisters_mailboxwrite for cpu1
	armlocalregisters_mailboxwrite_cpu1 = (armlocalregisters_mailboxwrite_t *)(ARMLOCALREGISTERS_MAILBOXWRITE_BASE + (1 * sizeof(armlocalregisters_mailboxwrite_t)));
	_XDPRINTFSMP_("%s: cpu 1: armlocalregisters_mailboxwrite at 0x%08x\n", __func__, armlocalregisters_mailboxwrite_cpu1);
	_XDPRINTFSMP_("%s: cpu 1: armlocalregisters_mailboxwrite->mailbox3write at 0x%08x\n", __func__, i, &armlocalregisters_mailboxwrite_cpu1->mailbox3write);

	//map armlocalregisters_mailboxreadclear for cpu1
	armlocalregisters_mailboxreadclear_cpu1 = (armlocalregisters_mailboxreadclear_t *)(ARMLOCALREGISTERS_MAILBOXREADCLEAR_BASE + (1 * sizeof(armlocalregisters_mailboxreadclear_t)));
	_XDPRINTFSMP_("%s: cpu 1: armlocalregisters_mailboxreadclear at 0x%08x\n", __func__, armlocalregisters_mailboxreadclear_cpu1);
	_XDPRINTFSMP_("%s: cpu 1: armlocalregisters_mailboxreadclear->mailbox3readclear at 0x%08x\n", __func__, i, &armlocalregisters_mailboxreadclear_cpu1->mailbox3readclear);


	/*for(i=1; i < BCM2837_MAXCPUS; i++){
		//map armlocalregisters_mailboxwrite
		armlocalregisters_mailboxwrite = (armlocalregisters_mailboxwrite_t *)(ARMLOCALREGISTERS_MAILBOXWRITE_BASE + (i * sizeof(armlocalregisters_mailboxwrite_t)));

		_XDPRINTFSMP_("%s: cpu %u: armlocalregisters_mailboxwrite at 0x%08x\n", __func__, i, armlocalregisters_mailboxwrite);
		_XDPRINTFSMP_("%s: cpu %u: armlocalregisters_mailboxwrite->mailbox3write at 0x%08x\n", __func__, i, &armlocalregisters_mailboxwrite->mailbox3write);
	}*/



}
