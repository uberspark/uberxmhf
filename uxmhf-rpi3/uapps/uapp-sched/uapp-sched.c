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
extern u32 uapp_sched_fiqhandler_stack[];

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
	u32 event;    		// set to TRUE at timeout
	int priority;		// priority associated with the timer
	TIME sticky_time_to_wait;  // relative time to wait sticky
	TIME time_to_wait;  // relative time to wait
};

volatile u32 fiq_sp = 0;
volatile u32 normal_sp = 0;


__attribute__((section(".data"))) struct sched_timer sched_timers[MAX_TIMERS];   // set of timers
__attribute__((section(".data"))) struct sched_timer *timer_next = NULL; // timer we expect to run down next
__attribute__((section(".data"))) TIME time_timer_set;    // time when physical timer was set

extern __attribute__(( section(".data") )) u32 priority_queue_lock=1;

__attribute__((section(".data"))) struct sched_timer timer_last = {
  FALSE,
  FALSE,
  0,
  VERY_LONG_TIME,
  VERY_LONG_TIME
};


__attribute__((section(".data"))) volatile u8 thread1_event = FALSE;
__attribute__((section(".data"))) volatile u8 thread2_event = FALSE;


//////
// priority queue implementation
//////

#define PRIORITY_QUEUE_SIZE 5

typedef struct {
	void *data; //data or pointer to data
	int priority; 	//priority (higher value = higher priority)
} priority_queue_t;


//first element [][0]=value, second element [][1] = priority
//__attribute__((section(".data"))) int priority_queue[PRIORITY_QUEUE_SIZE][2];

__attribute__((section(".data"))) priority_queue_t priority_queue[PRIORITY_QUEUE_SIZE];


#if 0
__attribute__((section(".data"))) int top = -1;
__attribute__((section(".data"))) int bottom;
#endif

#if 0
__attribute__((section(".data"))) int front = -1;
__attribute__((section(".data"))) int rear = -1;
#endif

__attribute__((section(".data"))) int priority_queue_totalelems = 0;

//maintain priority queue in descending order

// Function to check priority and place element
void check_and_insert(void *data, int priority){
	int i, j;

	for(i=0; i < priority_queue_totalelems; i++){
		if(priority > priority_queue[i].priority){
			//we found the index at which to insert (i)
			//move elements from i through priority_queue_totalelems-1 forward
			for(j=(priority_queue_totalelems-1); j>=i; j--){
				priority_queue[j+1].data = priority_queue[j].data;
				priority_queue[j+1].priority = priority_queue[j].priority;
			}
			//now insert at i
			priority_queue[i].data = data;
			priority_queue[i].priority = priority;
			return;
		}
	}

    priority_queue[i].data = data;
    priority_queue[i].priority = priority;
}

//return 0 on error, 1 on success
int priority_queue_insert(void *data, int priority){
	//return error if we are maxed out
	if(priority_queue_totalelems >= PRIORITY_QUEUE_SIZE ){
		_XDPRINTF_("%s,%u: Queue overflow, no more elements can be inserted!\n", __func__, __LINE__);
		return 0;
    }

	//if we have no elements then just plug value and priority as the first
	if(priority_queue_totalelems == 0){
		priority_queue[priority_queue_totalelems].data = data;
		priority_queue[priority_queue_totalelems].priority = priority;
		priority_queue_totalelems++;
	}else{
		//we have some elements so check and insert
		check_and_insert(data, priority);
		priority_queue_totalelems++;
	}

	return 1;
}

void priority_queue_display(void){
	int i;

	_XDPRINTF_("%s,%u: Dumping queue...\n", __func__, __LINE__);

	for(i=0; i < priority_queue_totalelems; i++){
		_XDPRINTF_("  index=%u: priority=%d, data=%u\n", i, priority_queue[i].priority,
					priority_queue[i].data);
	}

	_XDPRINTF_("%s,%u: Done.\n", __func__, __LINE__);
}


//return 0 on error, 1 on success
int priority_queue_remove(void *data, int *priority){
	int i;

	//return error if we have no elements
	if(priority_queue_totalelems == 0 ){
		//_XDPRINTFSMP_("%s,%u: No elements in queue!\n", __func__, __LINE__);
		return 0;
    }

	//return the top element
	*((u32 *)data) = priority_queue[0].data;
	*priority = priority_queue[0].priority;

	//move up everything else
	for(i=0; i < (priority_queue_totalelems-1); i++){
		priority_queue[i].data = priority_queue[i+1].data;
		priority_queue[i].priority = priority_queue[i+1].priority;
	}

	priority_queue_totalelems--;
	return 1;
}



#if 0
// Function to check priority and place element
void check(int value, int priority){
    int i,j;

    for (i = 0; i <= rear; i++){
        if (priority >= priority_queue[i][1]){
            for (j = rear + 1; j > i; j--){
                priority_queue[j][0] = priority_queue[j - 1][0];
            	priority_queue[j][1] = priority_queue[j - 1][1];
            }
            priority_queue[i][0] = value;
            priority_queue[i][1] = priority;
            return;
        }
    }

    priority_queue[i][0] = value;
    priority_queue[i][1] = priority;
}

//return 0 on error, 1 on success
int priority_queue_insert(int value, int priority){
    if (rear >= PRIORITY_QUEUE_SIZE - 1){
		_XDPRINTFSMP_("%s,%u: Queue overflow, no more elements can be inserted!\n", __func__, __LINE__);
		return 0;
    }

    //no elements so far, so just insert at the beginning
    if ((front == -1) && (rear == -1)){
        front++;
        rear++;
        priority_queue[rear][0] = value;
        priority_queue[rear][1] = priority;
    }else{ //we have some elements already so check and insert by priority
        check(value, priority);
        //point to the rear of the queue
        rear++;
    }

    return 1;
}
#endif







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
struct sched_timer *uapp_sched_timer_declare(u32 time, char *event, int priority){
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
  //t->event = event;
  t->event = FALSE;
  t->time_to_wait = time;
  t->sticky_time_to_wait = time;
  t->priority = priority;

  //_XDPRINTF_("%s,%u: event=%u, time_to_wait=%016llx, sticky_time_to_wait=%016llx, priority=%u\n",
	//	  __func__, __LINE__,
	//		t->event, t->time_to_wait, t->sticky_time_to_wait, t->priority);


  if (!timer_next) {
    // no timers set at all, so this is shortest
    time_timer_set = uapp_sched_read_cpucounter();
    uapp_sched_start_physical_timer((timer_next = t)->time_to_wait);
	//_XDPRINTF_("%s,%u: ENTER, time_to_wait=%016llx\n", __func__, __LINE__,
	//		t->time_to_wait);
  } else if ((time + uapp_sched_read_cpucounter()) < (timer_next->time_to_wait + time_timer_set)) {
    // new timer is shorter than current one, so
    uapp_sched_timers_update(uapp_sched_read_cpucounter() - time_timer_set);
    time_timer_set = uapp_sched_read_cpucounter();
    uapp_sched_start_physical_timer((timer_next = t)->time_to_wait);
	//_XDPRINTF_("%s,%u: ENTER\n", __func__, __LINE__);
  } else {
    // new timer is longer, than current one
	//_XDPRINTF_("%s,%u: ENTER, time_to_wait=%016llx\n", __func__, __LINE__,
	//		t->time_to_wait);
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

  //_XDPRINTF_("%s,%u: ENTER: time=%016llx\n", __func__, __LINE__, time);

  for (t=sched_timers;t<&sched_timers[MAX_TIMERS];t++) {
    if (t->inuse) {
      if (time < t->time_to_wait) { // unexpired
  		//_XDPRINTF_("%s,%u: ENTER: time_to_wait=%016llx\n", __func__, __LINE__,
  		//		t->time_to_wait);
  		//_XDPRINTF_("%s,%u: timer_next->time_to_wait=%016llx\n", __func__, __LINE__,
  		//		timer_next->time_to_wait);
  		t->time_to_wait -= time;
        if (t->time_to_wait < timer_next->time_to_wait){
          timer_next = t;
    		//_XDPRINTF_("%s,%u: ENTER\n", __func__, __LINE__);
        }
      } else { // expired
        /* tell scheduler */
		//_XDPRINTF_("%s,%u: ENTER\n", __func__, __LINE__);
    	t->event = TRUE;
        t->inuse = FALSE; 	// remove timer
		//spin_lock(&priority_queue_lock);
		//priority_queue_insert((void *)t, t->priority);
		//spin_unlock(&priority_queue_lock);
		//_XDPRINTFSMP_("%s,%u: inserted 0x%08x with priority=%d\n", __func__, __LINE__,
		//		t, t->priority);
		_XDPRINTFSMP_("\n%s: task timer priority=%d expired!\n", __func__, t->priority);
		uapp_sched_timer_declare(t->sticky_time_to_wait, NULL, t->priority);
      }
    }
  }

  /* reset timer_next if no timers found */
  if (!timer_next->inuse) {
	  timer_next = 0;
		//_XDPRINTF_("%s,%u: ENTER\n", __func__, __LINE__);
  }
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
// scheduler timer event processing
//////
void uapp_sched_process_timers(u32 cpuid){
	u32 i;
	u32 time_to_wait;
	int priority;

	for(i=0; i < MAX_TIMERS; i++){
		if(sched_timers[i].event){
			sched_timers[i].event = FALSE;
			priority_queue_insert((void *)&sched_timers[i], sched_timers[i].priority);
			//normal_sp = sysreg_read_sp();

			//_XDPRINTFSMP_("%s[%u]: normal_sp=0x%08x\n", __func__, cpuid, normal_sp);

			//_XDPRINTFSMP_("%s[%u]: timer expired; priority=%u, time_to_wait=%u\n", __func__, cpuid,
			//		sched_timers[i].priority, sched_timers[i].sticky_time_to_wait/ (1024*1024));
			time_to_wait = sched_timers[i].sticky_time_to_wait; //reload
			priority = sched_timers[i].priority;
			uapp_sched_timer_declare(time_to_wait, NULL, priority);
		}
	}
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

#if 0
	fiq_sp = sysreg_read_sp();
	_XDPRINTFSMP_("%s: Timer Fired: sp=0x%08x, cpsr=0x%08x!\n", __func__, fiq_sp,
			sysreg_read_cpsr());
	_XDPRINTFSMP_("%s: Halting!\n", __func__);
	HALT();
#endif


#if 1
	fiq_sp = sysreg_read_sp();
	//_XDPRINTFSMP_("%s: Timer Fired: sp=0x%08x, cpsr=0x%08x\n", __func__,
	//		fiq_sp, sysreg_read_cpsr());
	uapp_sched_timerhandler();
	//uapp_sched_start_physical_timer(3*1024*1024);
	//_XDPRINTFSMP_("%s: resuming\n", __func__);
#endif

#if 0
	fiq_sp = sysreg_read_sp();
	//_XDPRINTFSMP_("%s: Timer Fired: sp=0x%08x!\n", __func__, fiq_sp);
	bcm2837_miniuart_puts("\n FIQ timer fired: sp=0x");
	debug_hexdumpu32(fiq_sp);
	HALT();
	//uapp_sched_start_physical_timer(10 * 1024 * 1024);
#endif

}


void uapp_sched_timerhandler(void){
	uapp_sched_stop_physical_timer();
	//_XDPRINTFSMP_("%s,%u: ENTER\n", __func__, __LINE__);

	uapp_sched_timers_update(uapp_sched_read_cpucounter() - time_timer_set);

	// start physical timer for next shortest time if one exists
	if (timer_next) {
		//_XDPRINTFSMP_("%s, %u: starting physical timer with %u\n", __func__, __LINE__,
		//		timer_next->time_to_wait);
		time_timer_set = uapp_sched_read_cpucounter();
		uapp_sched_start_physical_timer(timer_next->time_to_wait);
	}

	//_XDPRINTFSMP_("%s,%u: ENTER\n", __func__, __LINE__);

}



void uapp_sched_initialize(u32 cpuid){
	int value;
	int priority;
	struct sched_timer *task_timer;
	u32 queue_data;
	int status;
	volatile u32 sp, spnew;


	if(cpuid == 0){
		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		//hypvtable_setentry(cpuid, 7, (u32)&uapp_sched_fiq_handler);
		uapp_sched_timer_initialize(cpuid);

		//_XDPRINTFSMP_("%s[%u]: Starting timers...\n", __func__, cpuid);

		//uapp_sched_timer_declare(3 * 1024 * 1024, NULL, 1);
		uapp_sched_timer_declare(9 * 1024 * 1024, NULL, 3);
		//uapp_sched_timer_declare(10 * 1024 * 1024, NULL, 3);

		_XDPRINTFSMP_("%s[%u]: Initializing scheduler...\n", __func__, cpuid);

		normal_sp =sysreg_read_sp();
		_XDPRINTFSMP_("%s[%u]: FIQ Stack pointer base=0x%08x\n", __func__, cpuid,
				&uapp_sched_fiqhandler_stack);
		_XDPRINTFSMP_("%s[%u]: normal_sp=0x%08x\n", __func__, cpuid, normal_sp);
		_XDPRINTFSMP_("%s[%u]: cpsr=0x%08x\n", __func__, cpuid, sysreg_read_cpsr());

	}else{
		_XDPRINTFSMP_("%s[%u]: AP CPU: nothing to do, moving on...\n", __func__, cpuid);
	}

}












#if 0

void uapp_sched_initialize(u32 cpuid){
	int value;
	int priority;
	struct sched_timer *task_timer;
	u32 queue_data;
	int status;
	volatile u32 sp, spnew;


#if 1
	if(cpuid == 0){
		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		//hypvtable_setentry(cpuid, 7, (u32)&uapp_sched_fiq_handler);
		uapp_sched_timer_initialize(cpuid);

		_XDPRINTFSMP_("%s[%u]: Starting timers...\n", __func__, cpuid);

		uapp_sched_timer_declare(3 * 1024 * 1024, NULL, 1);
		uapp_sched_timer_declare(9 * 1024 * 1024, NULL, 3);
		//uapp_sched_timer_declare(10 * 1024 * 1024, NULL, 3);

		_XDPRINTFSMP_("%s[%u]: Starting scheduler...\n", __func__, cpuid);

		normal_sp =sysreg_read_sp();
		_XDPRINTFSMP_("%s[%u]: FIQ Stack pointer base=0x%08x\n", __func__, cpuid,
				&uapp_sched_fiqhandler_stack);
		_XDPRINTFSMP_("%s[%u]: normal_sp=0x%08x\n", __func__, cpuid, normal_sp);
		_XDPRINTFSMP_("%s[%u]: cpsr=0x%08x\n", __func__, cpuid, sysreg_read_cpsr());

		while(1){
#if 0
			if(thread1_event){
				sp =sysreg_read_sp();
				_XDPRINTFSMP_("%s: thread1 timer expired: sp=0x%08x!\n", __func__, sp);
				thread1_event = FALSE;
				uapp_sched_timer_declare(3 * 1024 * 1024, &thread1_event, 1);
			}

			if(thread2_event){
				sp =sysreg_read_sp();
				_XDPRINTFSMP_("%s: thread2 timer expired: sp=0x%08x!\n", __func__, sp);
				thread2_event = FALSE;
				uapp_sched_timer_declare(6 * 1024 * 1024, &thread2_event, 3);
			}
#endif


#if 1
			uapp_sched_process_timers(cpuid);

			#if 1
			status=0;
			//spin_lock(&priority_queue_lock);
			status = priority_queue_remove(&queue_data, &priority);
			//spin_unlock(&priority_queue_lock);

			if(status){
				//_XDPRINTFSMP_("%s: got queue 0x%08x, priority=%u\n", __func__,
				//		queue_data, priority);

				task_timer = (struct sched_timer *)queue_data;
				_XDPRINTFSMP_("%s[%u]: task timer priority=%d expired!\n", __func__, cpuid, task_timer->priority);
			}
			#endif

			/*spnew =sysreg_read_sp();
			if(sp != spnew){
				_XDPRINTFSMP_("%s: we have some stack issues sp=0x%08x, spnew=0x%08x\n",
						__func__, sp, spnew);
				HALT();
			}*/
			/*status=0;
			spin_lock(&priority_queue_lock);
			//status = priority_queue_remove(&queue_data, &priority);
			spin_unlock(&priority_queue_lock);
			*/

			/*if(status){
				_XDPRINTFSMP_("%s: got queue 0x%08x, priority=%u\n", __func__,
						queue_data, priority);

				//task_timer = (struct sched_timer *)queue_data;
				//_XDPRINTFSMP_("%s: task timer priority=%d expired!\n", __func__, task_timer->priority);
			}*/
#endif


#if 0
			spnew =sysreg_read_sp();

			/*status=0;
			spin_lock(&priority_queue_lock);
			//status = priority_queue_remove(&queue_data, &priority);
			spin_unlock(&priority_queue_lock);
			*/

			/*if(status){
				_XDPRINTFSMP_("%s: got queue 0x%08x, priority=%u\n", __func__,
						queue_data, priority);

				//task_timer = (struct sched_timer *)queue_data;
				//_XDPRINTFSMP_("%s: task timer priority=%d expired!\n", __func__, task_timer->priority);
			}*/
#endif

		}

		HALT();

	}else{
		_XDPRINTFSMP_("%s[%u]: Halting AP CPU!\n", __func__, cpuid);
		HALT();
	}

#endif


#if 0
	if(cpuid == 0){
		_XDPRINTFSMP_("%s[%u]: Current CPU counter=0x%016llx\n", __func__, cpuid,
				uapp_sched_read_cpucounter());

		priority_queue_insert(10, 1);
		priority_queue_insert(11, 2);
		priority_queue_insert(12, 1);
		priority_queue_insert(13, 3);
		priority_queue_display();

		priority_queue_remove(&value, &priority);
		_XDPRINTFSMP_("%s: priority=%u, value=%u\n", __func__, priority, value);
		priority_queue_display();

		priority_queue_remove(&value, &priority);
		_XDPRINTFSMP_("%s: priority=%u, value=%u\n", __func__, priority, value);
		priority_queue_display();

		priority_queue_remove(&value, &priority);
		_XDPRINTFSMP_("%s: priority=%u, value=%u\n", __func__, priority, value);
		priority_queue_display();

		priority_queue_insert(13, 3);
		priority_queue_display();

		priority_queue_insert(40, 1);
		priority_queue_display();

		priority_queue_remove(&value, &priority);
		_XDPRINTFSMP_("%s: priority=%u, value=%u\n", __func__, priority, value);
		priority_queue_display();

		priority_queue_remove(&value, &priority);
		_XDPRINTFSMP_("%s: priority=%u, value=%u\n", __func__, priority, value);
		priority_queue_display();

		priority_queue_remove(&value, &priority);
		_XDPRINTFSMP_("%s: priority=%u, value=%u\n", __func__, priority, value);
		priority_queue_display();

		HALT();
	}
#endif

}

#endif
