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


//////////////////////////////////////////////////////////////////////////////
// mavlinkserhb async timer functions
//////////////////////////////////////////////////////////////////////////////


//////
// the periodic function which handles the heart-beat protocol
//////
void uapp_mavlinkserhb_handleheartbeat(struct sched_timer *t){
	bcm2837_miniuart_puts("mavlinkserhb: periodic heart-beat handler fired\n");
}

//////////////////////////////////////////////////////////////////////////////





//////////////////////////////////////////////////////////////////////////////
// mavlinkserhb hypercall APIs
//////////////////////////////////////////////////////////////////////////////

//////
// mavlinkserhb initialize hypercall API
// creates the heart-beat thread to begin processing mavlink heart-beat
// messages
//////
uapp_mavlinkserhb_handlehcall_initialize(uapp_mavlinkserhb_param_t *mlhbsp){


}



//////
// top-level hypercall handler hub
// return true if handled the hypercall, false if not
//////
bool uapp_mavlinkserhb_handlehcall(u32 uhcall_function, void *uhcall_buffer,
		u32 uhcall_buffer_len){
	uapp_mavlinkserhb_param_t *mlhbsp;

	if(uhcall_function != UAPP_MAVLINKSERHB_UHCALL){
		return false;
	}

	mlhbsp = (uapp_mavlinkserhb_param_t *)uhcall_buffer;

	if(mlhbsp->uhcall_fn == UAPP_MAVLINKSERHB_UHCALL_INITIALIZE){
		uapp_mavlinkserhb_handlehcall_initialize(mlhbsp);

	}else{
		//ignore unknown uhcall_fn silently

	}

	return true;
}


//////////////////////////////////////////////////////////////////////////////




//////////////////////////////////////////////////////////////////////////////
// mavlinkserhb initialization
//////////////////////////////////////////////////////////////////////////////

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
