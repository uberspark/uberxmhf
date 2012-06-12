/*! \file processor.h \brief LPC2100 Processor Initialization and Support. */
//*****************************************************************************
//
// File Name	: 'processor.h'
// Title		: LPC2100 Processor Initialization and Support
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

#ifndef PROCESSOR_H
#define PROCESSOR_H

//#include "global.h"

void processorInit(void);


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

/******************************************************************************
 * Macro Name: IENABLE()
 * Description:
 *	  Nested Interrupt Entry
 *    This macro enables interrupts, switch to System Mode and relevant stack operations
 *
 *****************************************************************************/
#define IENABLE()   asm volatile(" mrs   lr, spsr\n"      /* copy SPSR to LR */ \
                                 " stmfd sp!,{lr}\n"      /* save SPSR */ \
                                 " msr   cpsr_c, #0x1f\n" /* enable IRQ (Sys Mode) */ \
                                 " stmfd sp!,{lr}")		  /* save LR */
 
                                                                 
/******************************************************************************
 * Macro Name: IDISABLE()
 * Description:
 *	  Nested Interrupt Entry
 *    This macro enables interrupts, switch to System Mode and relevant stack operations
 *
 *****************************************************************************/
#define IDISABLE()   asm volatile(" ldmfd  sp!,{lr}\n"    /* restore LR */ \
								 " msr   cpsr_c, #0x92\n" /* disable IRQ (IRQ Mode) */ \
                                 " ldmfd sp!,{lr}\n" 	  /* restore SPSR to LR */ \
                                 " msr   spsr_cxsf, lr\n")/* copy LR to SPSR */
           
                                 
/*****************************************************************************
 * Function Name: disableIRQ()
 * Description:
 *    This function sets the IRQ disable bit in the status register
 * Calling Sequence: 
 *    void
 * Returns:
 *    previous value of CPSR
 *****************************************************************************/
unsigned disableIRQ(void);

/******************************************************************************
 *
 * Function Name: enableIRQ()
 *
 * Description:
 *    This function clears the IRQ disable bit in the status register
 *
 * Calling Sequence: 
 *    void
 *
 * Returns:
 *    previous value of CPSR
 *
 *****************************************************************************/
unsigned enableIRQ(void);

/******************************************************************************
 *
 * Function Name: restoreIRQ()
 *
 * Description:
 *    This function restores the IRQ disable bit in the status register
 *    to the value contained within passed oldCPSR
 *
 * Calling Sequence: 
 *    void
 *
 * Returns:
 *    previous value of CPSR
 *
 *****************************************************************************/
unsigned restoreIRQ(unsigned oldCPSR);

/******************************************************************************
 *
 * Function Name: disableFIQ()
 *
 * Description:
 *    This function sets the FIQ disable bit in the status register
 *
 * Calling Sequence: 
 *    void
 *
 * Returns:
 *    previous value of CPSR
 *
 *****************************************************************************/
unsigned disableFIQ(void);

/******************************************************************************
 *
 * Function Name: enableFIQ()
 *
 * Description:
 *    This function clears the FIQ disable bit in the status register
 *
 * Calling Sequence: 
 *    void
 *
 * Returns:
 *    previous value of CPSR
 *
 *****************************************************************************/
unsigned enableFIQ(void);

/******************************************************************************
 *
 * Function Name: restoreIRQ()
 *
 * Description:
 *    This function restores the FIQ disable bit in the status register
 *    to the value contained within passed oldCPSR
 *
 * Calling Sequence: 
 *    void
 *
 * Returns:
 *    previous value of CPSR
 *
 *****************************************************************************/
unsigned restoreFIQ(unsigned oldCPSR);

#endif
