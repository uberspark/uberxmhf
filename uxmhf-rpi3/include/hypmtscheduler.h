/*
	hypervisor mixed-trust scheduler

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __HYPMTSCHEDULER_H__
#define __HYPMTSCHEDULER_H__

#define UAPP_HYPMTSCHEDULER_UHCALL	0xC0

#define UAPP_HYPMTSCHEDULER_UHCALL_FNCREATEHYPTHREAD	1

#ifndef __ASSEMBLY__

#define TRUE  	1
#define FALSE 	0

#define MAX_TIMERS	4	//number of timers
typedef uint64_t TIME;   	//our time type; 64-bits since we are using clock cycles
#define VERY_LONG_TIME  0xffffffffffffffffULL	//longest time possible

struct sched_timer {
	uint32_t inuse;			// TRUE if in use
	uint32_t event;    		// set to TRUE at timeout
	int priority;		// priority associated with the timer
	TIME sticky_time_to_wait;  // relative time to wait sticky
	TIME time_to_wait;  // relative time to wait
};

typedef struct {
	uint8_t uhcall_fn;
	uint32_t iparam_1;
	uint32_t iparam_2;
	uint32_t status;
}ugapp_hypmtscheduler_param_t;


#endif // __ASSEMBLY__



#endif //__HYPMTSCHEDULER_H__
