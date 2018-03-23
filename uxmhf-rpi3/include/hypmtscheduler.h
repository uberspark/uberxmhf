/*
	hypervisor mixed-trust scheduler

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __HYPMTSCHEDULER_H__
#define __HYPMTSCHEDULER_H__


#ifndef __ASSEMBLY__

#define TRUE  	1
#define FALSE 	0

#define MAX_TIMERS	4	//number of timers
typedef u64 TIME;   	//our time type; 64-bits since we are using clock cycles
#define VERY_LONG_TIME  0xffffffffffffffffULL	//longest time possible

struct sched_timer {
	u32 inuse;			// TRUE if in use
	u32 event;    		// set to TRUE at timeout
	int priority;		// priority associated with the timer
	TIME sticky_time_to_wait;  // relative time to wait sticky
	TIME time_to_wait;  // relative time to wait
};


#endif // __ASSEMBLY__



#endif //__HYPMTSCHEDULER_H__
