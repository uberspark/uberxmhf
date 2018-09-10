/*
	MAVLINK serial heart-beat uberapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

//////////////////////////////////////////////////////////////////////////////
// headers
//////////////////////////////////////////////////////////////////////////////

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <hypmtscheduler.h>
#include <mavlinkserhb.h>

//////
// the periodic function which handles the heart-beat protocol
//////
void uapp_mavlinkserhb_handleheartbeat(struct sched_timer *t){

}


//////
// the main initialization function
//////
void uapp_mavlinkserhb_initialize(u32 cpuid){

	if(cpuid == 0){
		_XDPRINTFSMP_("%s[%u]: Initializing mavlinkserhb...\n", __func__, cpuid);

		//declare a timer to deal with heart-beat
		uapp_sched_timer_declare((0.5 * HYPMTSCHEDULER_TIME_1SEC),
				(0.5 * HYPMTSCHEDULER_TIME_1SEC), 99, &uapp_mavlinkserhb_handleheartbeat);

	}else{
		_XDPRINTFSMP_("%s[%u]: AP CPU: nothing to do, moving on...\n", __func__, cpuid);
	}


}


//////////////////////////////////////////////////////////////////////////////
