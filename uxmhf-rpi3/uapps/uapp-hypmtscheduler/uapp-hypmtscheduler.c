/*
	scheduler hypapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <hypmtscheduler.h>


//////
// externs
//////

extern void uapp_sched_fiq_handler(void);
extern u32 uapp_sched_fiqhandler_stack[];
extern u32 uapp_sched_fiqhandler_stack_top[];
extern __attribute__(( section(".data") )) u32 priority_queue_lock=1;
extern void uapp_hypmtsched_schedentry(void);

//////
// forward function prototypes
//////

u64 uapp_sched_read_cpucounter(void);
void_uapp_sched_logic(void);


//////
// global variables
//////

volatile u32 fiq_sp = 0;
volatile u32 fiq_cpsr = 0;
volatile u32 fiq_pemode= 0;
volatile u32 normal_sp = 0;

__attribute__((section(".data"))) volatile u32 fiq_timer_handler_timerevent_triggered = 0;
__attribute__((section(".data"))) volatile u32 fiq_timer_handler_guestmode_pc = 0;
__attribute__((section(".data"))) volatile u32 fiq_timer_handler_guestmode_spsr = 0;

__attribute__((section(".data"))) struct sched_timer sched_timers[MAX_TIMERS];   // set of timers
__attribute__((section(".data"))) struct sched_timer *timer_next = NULL; // timer we expect to run down next
__attribute__((section(".data"))) TIME time_timer_set;    // time when physical timer was set

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
	//disable_fiq();

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

	//enable_fiq();
}


//////
// declare a timer
// time = time to wait in clock ticks
// returns NULL if something went wrong
//////
struct sched_timer *uapp_sched_timer_declare(u32 time, char *event, int priority){
  struct sched_timer *t;

  //disable_fiq();

  for (t=sched_timers;t<&sched_timers[MAX_TIMERS];t++) {
    if (!t->inuse) break;
  }

  // out of timers?
  if (t == &sched_timers[MAX_TIMERS]) {
    //enable_fiq();
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
	//bcm2837_miniuart_puts("[HYPSCHED]: shortest timer set val=0x\n");
    //debug_hexdumpu32(t->time_to_wait);
	//bcm2837_miniuart_puts("\n");



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

  //enable_fiq();

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
        fiq_timer_handler_timerevent_triggered=1; //set timerevent_triggered to true
        //spin_lock(&priority_queue_lock);
		//priority_queue_insert((void *)t, t->priority);
		//spin_unlock(&priority_queue_lock);
		//_XDPRINTFSMP_("%s,%u: inserted 0x%08x with priority=%d\n", __func__, __LINE__,
		//		t, t->priority);
		//_XDPRINTFSMP_("\n%s: task timer priority=%d expired!\n", __func__, t->priority);
    	//bcm2837_miniuart_puts("\n[HYPSCHED]: Task timer expired. Priority=0x");
    	//debug_hexdumpu32(t->priority);
    	//bcm2837_miniuart_puts(" recorded.\n");

        //uapp_sched_timer_declare(t->sticky_time_to_wait, NULL, t->priority);
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
	//bcm2837_miniuart_puts("\n[HYPSCHED:start_physical_timer: period=0x");
	//debug_hexdumpu32((u32)time);
	//bcm2837_miniuart_puts("\n");

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




	//enable FIQs
	//enable_fiq();
	cpsr = sysreg_read_cpsr();
	_XDPRINTFSMP_("%s[%u]: CPSR[after enable_fiq]=0x%08x; CPSR.A=%u, CPSR.I=%u, CPSR.F=%u\n",
			__func__, cpuid, cpsr, ((cpsr & (1UL << 8)) >> 8),
			((cpsr & (1UL << 7)) >> 7),
			((cpsr & (1UL << 6)) >> 6) );

	_XDPRINTFSMP_("%s[%u]: EXIT\n", __func__, cpuid);
}


void uapp_sched_fiqhandler(u32 debug_val){
#if 0
	fiq_cpsr = sysreg_read_cpsr();
	bcm2837_miniuart_puts("\n[HYPTIMER]: Fired!: ");

	bcm2837_miniuart_puts("CPSR.A=0x");
	debug_hexdumpu32(((fiq_cpsr & (1UL << 8)) >> 8));
	bcm2837_miniuart_puts(" ");

	bcm2837_miniuart_puts("CPSR.I=0x");
	debug_hexdumpu32(((fiq_cpsr & (1UL << 7)) >> 7));
	bcm2837_miniuart_puts(" ");

	bcm2837_miniuart_puts("CPSR.F=0x");
	debug_hexdumpu32(((fiq_cpsr & (1UL << 6)) >> 6));
	bcm2837_miniuart_puts("\n");

	bcm2837_miniuart_puts("\n debug_val=0x");
	debug_hexdumpu32(debug_val);
	bcm2837_miniuart_puts("\n");

	bcm2837_miniuart_puts("\n sp=0x");
	debug_hexdumpu32(sysreg_read_sp());
	bcm2837_miniuart_puts("\n");

	bcm2837_miniuart_puts("\n stacktop=0x");
	debug_hexdumpu32(&uapp_sched_fiqhandler_stack_top);
	bcm2837_miniuart_puts("\n");


	//bcm2837_miniuart_puts("\n[HYPTIMER]: Halting!\n");
	//HALT();
#endif


	//fiq_sp = sysreg_read_sp();
	//_XDPRINTFSMP_("%s: Timer Fired: sp=0x%08x, cpsr=0x%08x\n", __func__,
	//		fiq_sp, sysreg_read_cpsr());
	//bcm2837_miniuart_puts("\n[HYPTIMER]: Fired!!\n");
	uapp_sched_timerhandler();
	//bcm2837_miniuart_puts("\n[HYPTIMER]: Fired!!\n");
	//uapp_sched_start_physical_timer(3 * 20 * 1024 * 1024);
	//_XDPRINTFSMP_("%s: resuming\n", __func__);

}


void uapp_sched_timerhandler(void){
	//bcm2837_miniuart_puts("\n[HYPTIMER]: Fired\n");

	//stop physical timer
	uapp_sched_stop_physical_timer();

	//set timerevent_triggered flag to false (0)
	fiq_timer_handler_timerevent_triggered=0;

	//update sw timers
	uapp_sched_timers_update(uapp_sched_read_cpucounter() - time_timer_set);

	// start physical timer for next shortest time if one exists
	if (timer_next) {
		time_timer_set = uapp_sched_read_cpucounter();
		uapp_sched_start_physical_timer(timer_next->time_to_wait);
	}

	if (fiq_timer_handler_timerevent_triggered == 0){
		//no timers expired so just return from timer interrupt
    	bcm2837_miniuart_puts("\n[HYPTIMER]: No timers expired EOI: elr_hyp=0x");
    	debug_hexdumpu32(sysreg_read_elrhyp());
    	bcm2837_miniuart_puts("spsr_hyp=0x");
    	debug_hexdumpu32(sysreg_read_spsr_hyp());
    	bcm2837_miniuart_puts("\n");
    	return;

	}else{
		//timer has expired, so let us look at the PE state
		//which triggered this timer FIQ to decide on our course of
		//action
		fiq_pemode = sysreg_read_spsr_hyp() & 0x0000000FUL;
		if(fiq_pemode == 0xA){
			//PE state was hyp mode, so we simply resume
	    	bcm2837_miniuart_puts("\n[HYPTIMER]: PE state=HYP, resuming\n");
			return;
		}else{
			//PE state says we are in guest mode
			fiq_timer_handler_guestmode_pc = sysreg_read_elrhyp();
			fiq_timer_handler_guestmode_spsr = sysreg_read_spsr_hyp();
	    	bcm2837_miniuart_puts("\n[HYPTIMER]: PE state=GUEST, PC=0x");
	    	debug_hexdumpu32(fiq_timer_handler_guestmode_pc);
	    	bcm2837_miniuart_puts(" SPSR=0x");
	    	debug_hexdumpu32(fiq_timer_handler_guestmode_spsr);
	    	bcm2837_miniuart_puts("\n");

	    	//bcm2837_miniuart_puts("Halting. Wip!\n");
	    	//HALT();

	    	//write scheduler main to elr_hyp
	    	//read spsr_hyp; change mode to hyp with all A, I and F masks set
	    	//0x000001DA
	    	//issue eret
	    	sysreg_write_elrhyp(&uapp_hypmtsched_schedentry);
	    	sysreg_write_spsr_hyp(0x000001DA);
	    	//cpu_eret();
	    	return;
		}
	}

	//uapp_sched_logic();
}





void uapp_sched_run_hyptasks(void){
	int status;
	u32 queue_data;
	int priority;
	struct sched_timer *task_timer;


	status=0;
	while(1){
		status = priority_queue_remove(&queue_data, &priority);
		if(status == 0)
			break;
		task_timer = (struct sched_timer *)queue_data;

		//interrupts enable
		enable_fiq();

		bcm2837_miniuart_puts("\n[HYPSCHED]: HypTask with Priority=0x");
    	debug_hexdumpu32(task_timer->priority);
		bcm2837_miniuart_puts(" has completed a run\n");


		//interrupts disable
		disable_fiq();
	}

}


void uapp_sched_logic(void){
	struct sched_timer *task_timer;
	u32 queue_data;
	int priority;
	int status;
	volatile u32 sp, spnew;

	//bcm2837_miniuart_puts("\n[HYPSCHED]: Came in. Halting Wip!\n");
	//HALT();

	uapp_sched_process_timers(0); //TBD: remove hard-coded cpuid (0)
	//uapp_sched_run_hyptasks();

	#if 1
	while(1){
		uapp_sched_run_hyptasks();
		uapp_sched_process_timers(0); //TBD: remove hard-coded cpuid (0)
		if(priority_queue_isempty())
			break;
	}
	#endif

	bcm2837_miniuart_puts("\n[HYPSCHED]: Finished all HypTasks. Now resuming guest...\n");
	//bcm2837_miniuart_puts("\n[HYPSCHED]: Halting WiP!\n");
	//HALT();

	//resume guest
	sysreg_write_elrhyp(fiq_timer_handler_guestmode_pc);
   	sysreg_write_spsr_hyp(fiq_timer_handler_guestmode_spsr);
   	fiq_timer_handler_guestmode_pc = 0;
   	fiq_timer_handler_guestmode_spsr = 0;
   	//cpu_eret();
   	return;
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
		//disable_fiq();
		//uapp_sched_timer_declare(9 * 1024 * 1024, NULL, 3);
		//enable_fiq();
		//uapp_sched_start_physical_timer(3 * 20 * 1024 * 1024);
		//uapp_sched_timer_declare(10 * 1024 * 1024, NULL, 3);

		uapp_sched_timer_declare(3 * 20 * 1024 * 1024, NULL, 1);
		//uapp_sched_timer_declare(9 * 20 * 1024 * 1024, NULL, 3);



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

//return true if handled the hypercall, false if not
bool uapp_hypmtscheduler_handlehcall(u32 uhcall_function, void *uhcall_buffer,
		u32 uhcall_buffer_len){
	ugapp_hypmtscheduler_param_t *hmtsp;
	uint32_t i;
	u32 uhcall_buffer_paddr;

	bcm2837_miniuart_puts("\nHYPSCHED:UHCALL: CPSR=0x");
	debug_hexdumpu32(sysreg_read_cpsr());
	bcm2837_miniuart_puts("\n");

	if(uhcall_function != UAPP_HYPMTSCHEDULER_UHCALL)
		return false;

	hmtsp = (ugapp_hypmtscheduler_param_t *)uhcall_buffer;

	if(hmtsp->uhcall_fn == UAPP_HYPMTSCHEDULER_UHCALL_FNCREATEHYPTHREAD){
		//_XDPRINTF_("%s: FNCREATEHYPTHREAD: period=0x%08x, priority=%u\n", __func__,
		//		hmtsp->iparam_1, hmtsp->iparam_2);
    	bcm2837_miniuart_puts("\n[HYPSCHED:FNCREATEHYPTHREAD]: period=0x");
    	debug_hexdumpu32(hmtsp->iparam_1);
    	bcm2837_miniuart_puts(" priority=0x\n");
    	debug_hexdumpu32(hmtsp->iparam_2);
    	bcm2837_miniuart_puts("\n");

		uapp_sched_timer_declare(hmtsp->iparam_1, NULL, hmtsp->iparam_2);
		//uapp_sched_timer_declare(9 * 20 * 1024 * 1024, NULL, 3);

		hmtsp->status=0;	//success

	}else{
		_XDPRINTF_("%s: uknown uhcall_fn=%u. Ignoring.\n",
				__func__, hmtsp->uhcall_fn);
	}

	return true;
}
