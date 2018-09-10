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

#include <mavlinkserhb.h>

//////
// the main initialization function
//////
void uapp_mavlinkserhb_initialize(u32 cpuid){

	if(cpuid == 0){
		_XDPRINTFSMP_("%s[%u]: Initializing mavlinkserhb...\n", __func__, cpuid);

	}else{
		_XDPRINTFSMP_("%s[%u]: AP CPU: nothing to do, moving on...\n", __func__, cpuid);
	}

}


//////////////////////////////////////////////////////////////////////////////
