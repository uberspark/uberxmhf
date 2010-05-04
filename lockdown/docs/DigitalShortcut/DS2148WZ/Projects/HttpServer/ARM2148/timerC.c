/*! \file timer.c \brief Timer Support Library for LPC2100. */
//*****************************************************************************
//
// File Name	: 'timerC.c'
// Title		: Timer Support for LPC2100
// Author		: JD - Copyright (C) 2008
// Created		: 2008.07.10
// Revised		: 2008.12.04
// Version		: 0.1
// Target MCU	: ARM processors
// Editor Tabs	: 2
//
//
//*****************************************************************************


#include "lpc21xx.h"
#include "processor.h"

#include "timerC.h"

#define IRQ_MASK 0x00000080

volatile unsigned int	miliSec;

void timer0Init(void);

//extern void timer1Init(void);
extern void	delay(unsigned long d);

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


typedef void (*voidFuncPtr)(void);
static volatile voidFuncPtr TimerIntrFunc[TIMER_NUM_INTERRUPTS];

extern	unsigned int	Event;


void timerInit(void)
{
	uint8 intNum;
	// detach all user functions from interrupts
	for(intNum=0; intNum<TIMER_NUM_INTERRUPTS; intNum++)
		timerDetach(intNum);

	// initialize timer0
	timer0Init();
	
	// initialize timer1
	//timer1Init();

	// enable interrupts
	enableIRQ();
}

/** Timer0 Interrupt Service Every 1mSec
**/
void timer0ISR(void) __attribute__((naked));
void timer0ISR(void)
{
	ISR_ENTRY();
	
	T0IR |= TIR_MR0I;			// clear MR0 Interrupt

	VICSoftIntClear = (1<<VIC_TIMER0);
	VICVectAddr = 0x00000000;             // clear this interrupt from the VIC
	Event |= Msec_1;
	
	miliSec++;
	
	ISR_EXIT();                           // recover registers and return
}



/** Timer0 Interrupt Init for 1mSec
**/
void timer0Init(void)
{
	T0PR = 0; 	// set prescaler
	
	// reset timer
	T0TCR = TCR_RESET;
	delay(2);
	// start timer
	T0TCR = TCR_ENABLE;

  //  Initialize TIMER0 interrupt
	VICIntSelect &= ~(1<<VIC_TIMER0);					// setup timer0 interrupt as IRQ
	VICVectCntl4 = VIC_ENABLE | VIC_TIMER0;		// assign VIC slot
	VICVectAddr4 = (unsigned int)timer0ISR;
	// enable interrupt
	VICIntEnable |= (1<<VIC_TIMER0);

	// setup MR0 value    -scz- to get 1ms tick
	T0MR0 = (60000000/1000)-1;
	
	// enable timer0 interrupt and reset on MR0 match
	T0MCR |= TMCR_MR0_I | TMCR_MR0_R;
	
	miliSec = 0;

}

void timer1Clear(void)
{
	T1TCR = TCR_RESET;
	delay(1);
	T1TCR = TCR_ENABLE;

}


void timerAttach(uint8 interruptNum, void (*userFunc)(void) )
{
	// make sure the interrupt number is within bounds
	if(interruptNum < TIMER_NUM_INTERRUPTS)
	{
		// set the interrupt function to run
		// the supplied user's function
		TimerIntrFunc[interruptNum] = userFunc;
	}
}

void timerDetach(uint8 interruptNum)
{
	// make sure the interrupt number is within bounds
	if(interruptNum < TIMER_NUM_INTERRUPTS)
	{
		// set the interrupt function to run nothing
		TimerIntrFunc[interruptNum] = 0;
	}
}

unsigned int getT0(void)
{
	unsigned int t;
	
	t = T0TC;
	return	t;
}

unsigned int getT1(void)
{
	unsigned int t;
	
	t = T1TC;
	return	t;
}
