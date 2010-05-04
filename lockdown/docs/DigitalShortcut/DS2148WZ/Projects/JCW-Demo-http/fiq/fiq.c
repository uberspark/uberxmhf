//
//  $Id: fiq.c 47 2008-10-05 03:20:49Z jcw $
//  $Revision: 47 $
//  $Author: jcw $
//  $Date: 2008-10-04 23:20:49 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/fiq/fiq.c $
//

#include <stdlib.h>
#include <string.h>

#include "FreeRTOS.h"

#include "../cpu/cpu.h"
#include "fiq.h"

//
//
//
static volatile unsigned int fiqCounter;

//
//
//
void fiqInit (void)
{
  SCB_PCONP |= SCB_PCONP_PCTIM1;

  VIC_IntSelect |= VIC_IntSelect_Timer1;
  VIC_IntEnable = VIC_IntEnable_Timer1;

  T1_PR = 0;
  T1_MR0 = configCPU_CLOCK_HZ / 8;
  T1_MCR = T_MCR_MR0R | T_MCR_MR0I;
}

int fiqEnable (void)
{
  unsigned int state = T1_TCR;

  //
  //  Only needed in case some used 'beep' command, which also use timer 1.
  //
  fiqInit ();

  T1_TCR = T_TCR_CE;

  return (state & T_TCR_CE) ? 1 : 0;
}

int fiqDisable (void)
{
  unsigned int state = T1_TCR;

  T1_TCR = T_TCR_CR;

  return (state & T_TCR_CE) ? 1 : 0;
}

unsigned int fiqGetCount (void)
{
  return fiqCounter;
}

void fiqClearCount (void)
{
  fiqCounter = 0;
}

void fiqISR (void) __attribute__ ((interrupt ("FIQ"))) __attribute__ ((noinline));
void fiqISR (void)
{
  ++fiqCounter;

  T1_IR = T_IR_MASK;
}

static void fiqISRNext (void) __attribute ((naked));
static void fiqISRNext (void)
{
}

unsigned char *fiqFIQISRCopyToRAM (void)
{
  static unsigned char *FIQInterrupt = NULL;

  if (!FIQInterrupt)
  {
    if ((FIQInterrupt = malloc ((unsigned int) fiqISRNext - (unsigned int) fiqISR)))
    {
      memcpy (FIQInterrupt, &fiqISR, (unsigned int) fiqISRNext - (unsigned int) fiqISR);
      cpuSetupFIQISR (FIQInterrupt);
    }
  }

  return FIQInterrupt;
}

