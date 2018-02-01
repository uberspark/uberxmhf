/*
	scheduler hypapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>


extern void uapp_sched_fiq_handler(void);

u64 uapp_sched_read_cpucounter(void);

//////
// global typedefs and variables
//////
#define TRUE  	1
#define FALSE 	0

#define MAX_TIMERS	4	//number of timers
typedef u64 TIME;   	//our time type; 64-bits since we are using clock cycles
#define VERY_LONG_TIME  0xffffffffffffffffULL	//longest time possible

struct sched_timer {
	u32 inuse;			// TRUE if in use
	TIME time_to_wait;  // relative time to wait
	u8 *event;    		// set to TRUE at timeout
};

__attribute__((section(".data"))) struct sched_timer sched_timers[MAX_TIMERS];   // set of timers
__attribute__((section(".data"))) struct sched_timer *timer_next = NULL; // timer we expect to run down next
__attribute__((section(".data"))) TIME time_timer_set;    // time when physical timer was set

__attribute__((section(".data"))) struct sched_timer timer_last = {
  FALSE,  VERY_LONG_TIME, NULL
};


__attribute__((section(".data"))) volatile u8 thread1_event = FALSE;
__attribute__((section(".data"))) volatile u8 thread2_event = FALSE;


//////
// priority queue implementation
//////

#define PRIORITY_QUEUE_SIZE 5

__attribute__((section(".data"))) int priority_queue[PRIORITY_QUEUE_SIZE][2] = {0};
__attribute__((section(".data"))) int top = -1;
__attribute__((section(".data"))) int bottom;




//////
// initialize timer data structures
//////
void uapp_sched_timers_init(void){
  u32 i;

  for(i=0; i < MAX_TIMERS; i++)
	  sched_timers[i].inuse = FALSE;
}


//////
// enable FIQs
//////
void enable_fiq(void){
	u32 cpsr;
	cpsr = sysreg_read_cpsr();
	cpsr &= ~(1UL << 6);	//clear CPSR.F to allow FIQs
	sysreg_write_cpsr(cpsr);
}

//////
// disable FIQs
//////
void disable_fiq(void){
	u32 cpsr;
	cpsr = sysreg_read_cpsr();
	cpsr |= (1UL << 6);	//set CPSR.F to prevent FIQs
	sysreg_write_cpsr(cpsr);
}



//////
// undeclare (and disable) a timer
//////
void uapp_sched_timer_undeclare(struct sched_timer *t){
	disable_fiq();

	if (!t->inuse) {
		enable_fiq();
		return;
	}

	t->inuse = FALSE;

	// check if we were waiting on this one
	if (t == timer_next) {
		uapp_sched_timers_update(uapp_sched_read_cpucounter() - time_timer_set);
		if (timer_next) {
			uapp_sched_start_physical_timer(timer_next->time_to_wait);
			time_timer_set = uapp_sched_read_cpucounter();
		}
	}

	enable_fiq();
}


//////
// declare a timer
// time = time to wait in clock ticks
// returns NULL if something went wrong
//////
struct sched_timer *uapp_sched_timer_declare(u32 time, char *event){
  struct sched_timer *t;

  disable_fiq();

  for (t=sched_timers;t<&sched_timers[MAX_TIMERS];t++) {
    if (!t->inuse) break;
  }

  // out of timers?
  if (t == &sched_timers[MAX_TIMERS]) {
    enable_fiq();
    return(0);
  }

  // install new timer
  t->event = event;
  t->time_to_wait = time;
  if (!timer_next) {
    // no timers set at all, so this is shortest
    time_timer_set = uapp_sched_read_cpucounter();
    uapp_sched_start_physical_timer((timer_next = t)->time_to_wait);
	//_XDPRINTFSMP_("%s,%u: ENTER\n", __func__, __LINE__);
  } else if ((time + uapp_sched_read_cpucounter()) < (timer_next->time_to_wait + time_timer_set)) {
    // new timer is shorter than current one, so
    uapp_sched_timers_update(uapp_sched_read_cpucounter() - time_timer_set);
    time_timer_set = uapp_sched_read_cpucounter();
    uapp_sched_start_physical_timer((timer_next = t)->time_to_wait);
	//_XDPRINTFSMP_("%s,%u: ENTER\n", __func__, __LINE__);
  } else {
    // new timer is longer, than current one
	//_XDPRINTFSMP_("%s,%u: ENTER\n", __func__, __LINE__);
  }

  t->inuse = TRUE;

  enable_fiq();

  return(t);
}


//////
// subtract time from all timers, enabling those that run out
//////
void uapp_sched_timers_update(TIME time){
  struct sched_timer *t;

  timer_next = &timer_last;

  for (t=sched_timers;t<&sched_timers[MAX_TIMERS];t++) {
    if (t->inuse) {
      if (time < t->time_to_wait) { // unexpired
  		//_XDPRINTFSMP_("%s,%u: ENTER\n", __func__, __LINE__);
    	t->time_to_wait -= time;
        if (t->time_to_wait < timer_next->time_to_wait)
          timer_next = t;
      } else { // expired
        /* tell scheduler */
		//_XDPRINTFSMP_("%s,%u: ENTER\n", __func__, __LINE__);
    	*t->event = TRUE;
        t->inuse = FALSE; 	// remove timer
      }
    }
  }

  /* reset timer_next if no timers found */
  if (!timer_next->inuse) timer_next = 0;
}


//////
// read current physical counter for the CPU; we use this as current time
//////
u64 uapp_sched_read_cpucounter(void){
	return sysreg_read_cntpct();
}


//////
// start physical timer to fire off after specified clock ticks
//////
void uapp_sched_start_physical_timer(TIME time){
	//_XDPRINTFSMP_("%s: time=%u\n", __func__, (u32)time);

	sysreg_write_cnthp_tval(time);
	sysreg_write_cnthp_ctl(0x1);
}

//////
// stop physical timer
//////
void uapp_sched_stop_physical_timer(void){
	sysreg_write_cnthp_ctl(0x0);
}




//////
// uapp sched timer_initialize
// initialize hypervisor timer functionality
//////
void uapp_sched_timer_initialize(u32 cpuid){
	u32 cpsr;
	u64 cntpct_val;
	u32 cpu0_tintctl_value;
	u32 loop_counter=0;

	_XDPRINTFSMP_("%s[%u]: ENTER\n", __func__, cpuid);

	//disable FIQs
	disable_fiq();
	cpsr = sysreg_read_cpsr();
	_XDPRINTFSMP_("%s[%u]: CPSR[after disable_fiq]=0x%08x; CPSR.A=%u, CPSR.I=%u, CPSR.F=%u\n",
			__func__, cpuid, cpsr, ((cpsr & (1UL << 8)) >> 8),
			((cpsr & (1UL << 7)) >> 7),
			((cpsr & (1UL << 6)) >> 6) );


	//enable cpu0 timer interrupt control to generate FIQs
	cpu0_tintctl_value = mmio_read32(LOCAL_TIMER_INT_CONTROL0);
	_XDPRINTFSMP_("%s[%u]: cpu0_tintctl_value[before]=0x%08x, CNTHPFIQ=%u, CNTHPIRQ=%u\n",
			__func__, cpuid,
			cpu0_tintctl_value,
			((cpu0_tintctl_value & (1UL << 6)) >> 6),
			((cpu0_tintctl_value & (1UL << 2)) >> 2)
			);

	cpu0_tintctl_value &= ~(1UL << 2); //disable IRQs
	cpu0_tintctl_value |= (1UL << 6); //enable FIQs
	mmio_write32(LOCAL_TIMER_INT_CONTROL0, cpu0_tintctl_value);


	cpu0_tintctl_value = mmio_read32(LOCAL_TIMER_INT_CONTROL0);
	_XDPRINTFSMP_("%s[%u]: cpu0_tintctl_value[after]=0x%08x, CNTHPFIQ=%u, CNTHPIRQ=%u\n",
			__func__, cpuid,
			cpu0_tintctl_value,
			((cpu0_tintctl_value & (1UL << 6)) >> 6),
			((cpu0_tintctl_value & (1UL << 2)) >> 2)
			);



#if 0
	_XDPRINTFSMP_("%s[%u]: CNTHP_TVAL[initial]=%d\n", __func__, cpuid, sysreg_read_cnthp_tval());
	//sysreg_write_cnthp_tval(10*1024*1024);
	uapp_sched_start_physical_timer(10 * 1024 * 1024);
	_XDPRINTFSMP_("%s[%u]: CNTHP_TVAL[reset]=%d\n", __func__, cpuid, sysreg_read_cnthp_tval());

	sysreg_write_cnthp_ctl(0x1);
	_XDPRINTFSMP_("%s[%u]: CNTHP_TVAL[current]=%d\n", __func__, cpuid, sysreg_read_cnthp_tval());
	_XDPRINTFSMP_("%s[%u]: CNTHP_CTL[current]=%d\n", __func__, cpuid, sysreg_read_cnthp_ctl());
#endif

	//enable FIQs
	enable_fiq();
	cpsr = sysreg_read_cpsr();
	_XDPRINTFSMP_("%s[%u]: CPSR[after enable_fiq]=0x%08x; CPSR.A=%u, CPSR.I=%u, CPSR.F=%u\n",
			__func__, cpuid, cpsr, ((cpsr & (1UL << 8)) >> 8),
			((cpsr & (1UL << 7)) >> 7),
			((cpsr & (1UL << 6)) >> 6) );

	_XDPRINTFSMP_("%s[%u]: EXIT\n", __func__, cpuid);
}


void uapp_sched_fiqhandler(void){
#if 1
	uapp_sched_timerhandler();
#endif

#if 0
	_XDPRINTFSMP_("%s: Timer Fired!\n", __func__);

	uapp_sched_start_physical_timer(10 * 1024 * 1024);
#endif

}


void uapp_sched_timerhandler(void){
	uapp_sched_stop_physical_timer();
	//_XDPRINTFSMP_("%s,%u: ENTER\n", __func__, __LINE__);

	uapp_sched_timers_update(uapp_sched_read_cpucounter() - time_timer_set);

	// start physical timer for next shortest time if one exists
	if (timer_next) {
		//_XDPRINTFSMP_("%s, %u: ENTER\n", __func__, __LINE__);
		time_timer_set = uapp_sched_read_cpucounter();
		uapp_sched_start_physical_timer(timer_next->time_to_wait);
	}
}




void uapp_sched_initialize(u32 cpuid){


	if(cpuid == 0){
		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		hypvtable_setentry(cpuid, 7, (u32)&uapp_sched_fiq_handler);
		uapp_sched_timer_initialize(cpuid);

		#if 0
		_XDPRINTFSMP_("%s[%u]: Starting first timer...\n", __func__, cpuid);
		uapp_sched_start_physical_timer(10 * 1024 * 1024);
		#endif

		_XDPRINTFSMP_("%s[%u]: Starting first timer...\n", __func__, cpuid);

		uapp_sched_timer_declare(3 * 1024 * 1024, &thread1_event);
		uapp_sched_timer_declare(10 * 1024 * 1024, &thread2_event);

		_XDPRINTFSMP_("%s[%u]: Going into endless loop...\n", __func__, cpuid);
		while(1){
			if(thread1_event){
				//_XDPRINTFSMP_("%s[%u]: thread1 timer expired!\n", __func__, cpuid);
				_XDPRINTFSMP_("%s: thread1 timer expired!\n", __func__);
				thread1_event = FALSE;
				uapp_sched_timer_declare(3 * 1024 * 1024, &thread1_event);
			}

			if(thread2_event){
				//_XDPRINTFSMP_("%s[%u]: thread2 timer expired!\n", __func__, cpuid);
				_XDPRINTFSMP_("%s: thread2 timer expired!\n", __func__);
				thread2_event = FALSE;
				uapp_sched_timer_declare(10 * 1024 * 1024, &thread2_event);
			}


		}
		HALT();
	}
}

