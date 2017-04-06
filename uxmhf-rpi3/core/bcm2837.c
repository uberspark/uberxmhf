/*
	BCM2837 (pi3) specific functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

extern void secondary_cpu_entry(void);
volatile u32 cpu_smpready[BCM2837_MAXCPUS] = {1, 0, 0, 0};

void bcm2837_platform_initialize(void){

}


void bcm2837_platform_smpinitialize(void){
	u32 i;
	armlocalregisters_mailboxwrite_t *armlocalregisters_mailboxwrite;
	armlocalregisters_mailboxreadclear_t *armlocalregisters_mailboxreadclear;
	u32 timeout=20;

	for(i=1; i < BCM2837_MAXCPUS; i++){
		armlocalregisters_mailboxwrite = (armlocalregisters_mailboxwrite_t *)(ARMLOCALREGISTERS_MAILBOXWRITE_BASE + (i * sizeof(armlocalregisters_mailboxwrite_t)));
		armlocalregisters_mailboxreadclear = (armlocalregisters_mailboxreadclear_t *)(ARMLOCALREGISTERS_MAILBOXREADCLEAR_BASE + (i * sizeof(armlocalregisters_mailboxreadclear_t)));

		_XDPRINTFSMP_("%s: cpu %u: armlocalregisters_mailboxwrite at 0x%08x\n", __func__, i, armlocalregisters_mailboxwrite);
		_XDPRINTFSMP_("%s: cpu %u: armlocalregisters_mailboxwrite->mailbox3write at 0x%08x\n", __func__, i, &armlocalregisters_mailboxwrite->mailbox3write);

		cpu_dsb();
		if( armlocalregisters_mailboxreadclear->mailbox3readclear != 0){
			_XDPRINTFSMP_("%s: cpu %u: failed to respond. Halting!\n", __func__, i);
			HALT();
		}

		//write cpu execution start address
		armlocalregisters_mailboxwrite->mailbox3write = (u32)&secondary_cpu_entry;

		while (--timeout > 0) {
			if (armlocalregisters_mailboxreadclear->mailbox3readclear == 0) break;
			cpu_dmbish();
		}

		if (timeout==0){
			_XDPRINTFSMP_("%s: cpu %u failed to start. Halting!\n", __func__, i);
			HALT();
		}

		while(!cpu_smpready[i]){
			cpu_dmbish();
		}

		_XDPRINTFSMP_("%s: cpu-%u started successfully\n", __func__, i);
	}

}
