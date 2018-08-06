/*
	hypervisor mixed-trust scheduler

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __HYPMTSCHEDULER_H__
#define __HYPMTSCHEDULER_H__

#define UAPP_HYPMTSCHEDULER_UHCALL	0xC0

#define UAPP_HYPMTSCHEDULER_UHCALL_CREATEHYPTASK	1
#define UAPP_HYPMTSCHEDULER_UHCALL_DISABLEHYPTASK	2
#define UAPP_HYPMTSCHEDULER_UHCALL_DELETEHYPTASK	3
#define UAPP_HYPMTSCHEDULER_UHCALL_GETRAWTICK		4
#define UAPP_HYPMTSCHEDULER_UHCALL_INITTSC			5


#define HYPMTSCHEDULER_MAX_HYPTASKID	4
#define HYPMTSCHEDULER_MAX_HYPTASKS		4



#ifndef __ASSEMBLY__

#define TRUE  	1
#define FALSE 	0

#define MAX_TIMERS	4	//number of timers
typedef uint64_t TIME;   	//our time type; 64-bits since we are using clock cycles
#define VERY_LONG_TIME  0xffffffffffffffffULL	//longest time possible

#define HYPMTSCHEDULER_TIME_1SEC			19200000UL
//#define HYPMTSCHEDULER_TIME_1SEC			15518102UL
#define HYPMTSCHEDULER_TIME_1MSEC			(HYPMTSCHEDULER_1SEC / 1000)
#define HYPMTSCHEDULER_TIME_1USEC			(HYPMTSCHEDULER_1MSEC / 1000)

struct sched_timer;

typedef void (*HYPTHREADFUNC)(struct sched_timer *);

struct sched_timer {
	uint32_t inuse;			// TRUE if in use
	uint32_t event;    		// set to TRUE at timeout
	uint32_t disable_tfunc;	// set to TRUE if tfunc should not be invoked
	int priority;		// priority associated with the timer
	int first_time_period_expired;	//1 if first_time_period has expired, 0 otherwise
	TIME sticky_time_to_wait;  // relative time to wait sticky
	TIME regular_time_period;	//the regular time period of this timer
	TIME first_time_period; //the first time period of this timer
	TIME time_to_wait;  // relative time to wait
	HYPTHREADFUNC tfunc;	//the hypthread function associated with the timer
};

typedef struct {
	uint8_t uhcall_fn;
	uint32_t iparam_1;
	uint32_t iparam_2;
	uint32_t iparam_3;
	uint32_t iparam_4;
	uint32_t oparam_1;
	uint32_t oparam_2;
	uint32_t status;
}ugapp_hypmtscheduler_param_t;


typedef struct {
	uint32_t inuse;
	uint32_t hyptask_id;
	struct sched_timer *t;
}hypmtscheduler_hyptask_handle_t;



#endif // __ASSEMBLY__



#endif //__HYPMTSCHEDULER_H__
