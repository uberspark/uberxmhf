/*! \file timer.c \brief Timer Support Library for LPC2100. */
//*****************************************************************************
//
// File Name	: 'timerC.c'
// Title		: Timer Support Library for LPC2100
// Author		: Pascal Stang - Copyright (C) 2004
// Created		: 2004.05.05
// Revised		: 2004.07.12
// Version		: 0.1
// Target MCU	: ARM processors
// Editor Tabs	: 4
//
// NOTE: This code is currently below version 1.0, and therefore is considered
// to be lacking in some functionality or documentation, or may not be fully
// tested.  Nonetheless, you can expect most functions to work.
//
// This code is distributed under the GNU Public License
//		which can be found at http://www.gnu.org/licenses/gpl.txt
//
//*****************************************************************************

#include "type.h"
#include "lpc21xx.h"

#include "timerC.h"

// Forward Prototypes
unsigned enableIRQ(void);


#define	FREQ100kHz	100000			// Service Frequency in Hz - jd 100kHz = 10usec interval
#define	FREQ50Hz	50				// Slow Frequency in Hz - jd 50Hz 

/******************************************************************************
 *
 * MACRO Name: ISR_ENTRY()
 *
 * Description:
 *    This MACRO is used upon entry to an ISR.  The current version of
 *    the gcc compiler for ARM does not produce correct code for
 *    interrupt routines to operate properly with THUMB code.  The MACRO
 *    performs the following steps:
 *
 *    1 - Adjust address at which execution should resume after servicing
 *        ISR to compensate for IRQ entry
 *    2 - Save the non-banked registers r0-r12 and lr onto the IRQ stack.
 *    3 - Get the status of the interrupted program is in SPSR.
 *    4 - Push it onto the IRQ stack as well.
 *
 *****************************************************************************/
#define ISR_ENTRY() asm volatile(" sub   lr, lr,#4\n" \
                                 " stmfd sp!,{r0-r12,lr}\n" \
                                 " mrs   r1, spsr\n" \
                                 " stmfd sp!,{r1}")

/******************************************************************************
 *
 * MACRO Name: ISR_EXIT()
 *
 * Description:
 *    This MACRO is used to exit an ISR.  The current version of the gcc
 *    compiler for ARM does not produce correct code for interrupt
 *    routines to operate properly with THUMB code.  The MACRO performs
 *    the following steps:
 *
 *    1 - Recover SPSR value from stack       
 *    2 - and restore  its value                   
 *    3 - Pop the return address & the saved general registers from
 *        the IRQ stack & return
 *
 *****************************************************************************/
#define ISR_EXIT()  asm volatile(" ldmfd sp!,{r1}\n" \
                                 " msr   spsr_c,r1\n" \
                                 " ldmfd sp!,{r0-r12,pc}^")


#define IRQ_MASK 0x00000080

static inline unsigned __get_cpsr(void)
{
  unsigned long retval;
  asm volatile (" mrs  %0, cpsr" : "=r" (retval) : /* no inputs */  ); 
  return retval;
}

static inline void __set_cpsr(unsigned val)
{
  asm volatile (" msr  cpsr, %0" : /* no outputs */ : "r" (val)  );	
}


unsigned enableIRQ(void)
{
  unsigned _cpsr;

  _cpsr = __get_cpsr();
  __set_cpsr(_cpsr & ~IRQ_MASK);
  return _cpsr;
}


typedef void (*voidFuncPtr)(void);
static volatile voidFuncPtr TimerIntrFunc[TIMER_NUM_INTERRUPTS];

volatile unsigned int Timer0Pause;

extern  unsigned int		Event;

void delay(unsigned long d)
{
	for(; d; --d)
	{
		asm volatile ("nop");
	}
}


void timerInit(void)
{
	U8 intNum;
	// detach all user functions from interrupts
	for(intNum=0; intNum<TIMER_NUM_INTERRUPTS; intNum++)
		timerDetach(intNum);

	// initialize timer0
	timer0Init();
	
	// enable interrupts
	enableIRQ();
}

/** Timer0 Interrupt Init for 1mSec
**/
void timer0Init(void)
{
	// setup timer0
	// set prescaler
	T0PR = 0;
	
	// reset timer
	T0TCR = TCR_RESET;
	delay(2);
	
	// start timer
	T0TCR = TCR_ENABLE;

	// setup timer0 for IRQ
	// set interrupt as IRQ
	VICIntSelect &= ~(1<<VIC_TIMER0);
	// assign VIC slot
	VICVectCntl4 = VIC_ENABLE | VIC_TIMER0;
	VICVectAddr4 = (unsigned int)timer0Service;
	// enable interrupt
	VICIntEnable |= (1<<VIC_TIMER0);

	// setup MR0 value    -scz- to get 1ms tick
	T0MR0 = 60000000/1000;
	
	// enable timer0 interrupt and reset on MR0 match
	T0MCR |= TMCR_MR0_I | TMCR_MR0_R;

}

/** Timer0 Interrupt Service Every 1mSec
**/
void timer0Service(void)
{
	ISR_ENTRY();
	
	T0IR |= TIR_MR0I;			// clear MR0 Interrupt

	VICSoftIntClear = (1<<VIC_TIMER0);
	VICVectAddr = 0x00000000;             // clear this interrupt from the VIC
	Event |= Msec_1;
	
	ISR_EXIT();                           // recover registers and return
}

void timerAttach(U8 interruptNum, void (*userFunc)(void) )
{
	// make sure the interrupt number is within bounds
	if(interruptNum < TIMER_NUM_INTERRUPTS)
	{
		// set the interrupt function to run
		// the supplied user's function
		TimerIntrFunc[interruptNum] = userFunc;
	}
}

void timerDetach(U8 interruptNum)
{
	// make sure the interrupt number is within bounds
	if(interruptNum < TIMER_NUM_INTERRUPTS)
	{
		// set the interrupt function to run nothing
		TimerIntrFunc[interruptNum] = 0;
	}
}


