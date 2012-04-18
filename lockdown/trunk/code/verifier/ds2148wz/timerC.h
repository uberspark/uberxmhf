/*! \file timer.h \brief Timer Support Library for LPC2100. */
//*****************************************************************************
//
// File Name	: 'timer.h'
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

#ifndef TIMERC_H
#define TIMERC_H

//typedef unsigned char		uint8;		/**< unsigned 8-bit */

// defines
#define TIMER0MATCH0_INT		0
#define TIMER0MATCH1_INT		1
#define TIMER0MATCH2_INT		2
#define TIMER0MATCH3_INT		3
#define TIMER0CAPTURE0_INT		4
#define TIMER0CAPTURE1_INT		5
#define TIMER0CAPTURE2_INT		6

#define TIMER_NUM_INTERRUPTS	16

// Event Definitions
#define Msec_1		0x00400000

// functions
void delay(unsigned long d);

void timerInit(void);
void timer0Init(void);

//! Attach a user function to a timer interrupt
void timerAttach(U8 interruptNum, void (*userFunc)(void) );
//! Detach a user function from a timer interrupt
void timerDetach(U8 interruptNum);

void timer0Service(void) __attribute__((naked));

#endif
