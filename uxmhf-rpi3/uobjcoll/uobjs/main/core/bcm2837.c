/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
	BCM2837 (pi3) specific functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>
//#include <uberspark/include/uberspark.h>

CASM_FUNCDECL(void secondary_cpu_entry(void *noparam));
volatile u32 cpu_smpready[BCM2837_MAXCPUS] = {1, 0, 0, 0};

void bcm2837_platform_initialize(void){

}


void bcm2837_platform_smpinitialize(void){
	u32 i;
	armlocalregisters_mailboxwrite_t *armlocalregisters_mailboxwrite;
	armlocalregisters_mailboxreadclear_t *armlocalregisters_mailboxreadclear;
	armlocalregisters_mailboxreadclear_t *armlocalregisters_mailboxreadclear_cpu0;

	u32 timeout=20;

	armlocalregisters_mailboxreadclear_cpu0 = (armlocalregisters_mailboxreadclear_t *)(ARMLOCALREGISTERS_MAILBOXREADCLEAR_BASE + (0 * sizeof(armlocalregisters_mailboxreadclear_t)));

	for(i=1; i < BCM2837_MAXCPUS; i++){
	//for(i=1; i < 2; i++){
		timeout=20;
		armlocalregisters_mailboxwrite = (armlocalregisters_mailboxwrite_t *)(ARMLOCALREGISTERS_MAILBOXWRITE_BASE + (i * sizeof(armlocalregisters_mailboxwrite_t)));
		armlocalregisters_mailboxreadclear = (armlocalregisters_mailboxreadclear_t *)(ARMLOCALREGISTERS_MAILBOXREADCLEAR_BASE + (i * sizeof(armlocalregisters_mailboxreadclear_t)));

		_XDPRINTF_("%s: cpu %u: armlocalregisters_mailboxwrite at 0x%08x\n", __func__, i, armlocalregisters_mailboxwrite);
		_XDPRINTF_("%s: cpu %u: armlocalregisters_mailboxwrite->mailbox3write at 0x%08x\n", __func__, i, &armlocalregisters_mailboxwrite->mailbox3write);

		cpu_dsb();
		if( armlocalregisters_mailboxreadclear->mailbox3readclear != 0){
			_XDPRINTF_("%s: cpu %u: failed to respond. Halting!\n", __func__, i);
			HALT();
		}

		//write cpu execution start address
		armlocalregisters_mailboxwrite->mailbox3write = (u32)&secondary_cpu_entry;

		while (--timeout > 0) {
			if (armlocalregisters_mailboxreadclear->mailbox3readclear == 0) break;
			cpu_dmbish();
		}

		if (timeout==0){
			_XDPRINTF_("%s: cpu %u failed to start. Halting!\n", __func__, i);
			HALT();
		}

		while(armlocalregisters_mailboxreadclear_cpu0->mailbox3readclear == 0){
			cpu_dmbish();
			cpu_dsb();
		}

		armlocalregisters_mailboxreadclear_cpu0->mailbox3readclear = 1;

		//while(!cpu_smpready[i]){
		//	cpu_dmbish();
		//	cpu_dsb();
		//}

		_XDPRINTF_("%s: cpu-%u started successfully\n", __func__, i);
	}

}



u32 bcm2837_platform_waitforstartup(u32 cpuid){
	armlocalregisters_mailboxwrite_t *armlocalregisters_mailboxwrite;
	armlocalregisters_mailboxreadclear_t *armlocalregisters_mailboxreadclear;
	u32 cpu_startaddr=0;
	u32 retval=0;

	//_XDPRINTFSMP_("%s[%u]: ENTER\n", __func__, cpuid);

	armlocalregisters_mailboxwrite = (armlocalregisters_mailboxwrite_t *)(ARMLOCALREGISTERS_MAILBOXWRITE_BASE + (cpuid * sizeof(armlocalregisters_mailboxwrite_t)));
	armlocalregisters_mailboxreadclear = (armlocalregisters_mailboxreadclear_t *)(ARMLOCALREGISTERS_MAILBOXREADCLEAR_BASE + (cpuid * sizeof(armlocalregisters_mailboxreadclear_t)));


	//_XDPRINTFSMP_("%s[%u]: Waiting on mailbox startup signal...\n", __func__, cpuid);

	while(1){
		cpu_startaddr=armlocalregisters_mailboxreadclear->mailbox3readclear;
		if(cpu_startaddr != 0) break;
	}

	//_XDPRINTFSMP_("%s[%u]: Got startup signal, address=0x%08x\n", __func__, cpuid, cpu_startaddr);

	armlocalregisters_mailboxreadclear->mailbox3readclear = cpu_startaddr;

	retval = cpu_startaddr;
	cpu_startaddr=armlocalregisters_mailboxreadclear->mailbox3readclear;
	//_XDPRINTFSMP_("%s[%u]: Cleared mailbox [val=0x%08x] and ready to go\n", __func__, cpuid,
	//		cpu_startaddr);

	return retval;
}
