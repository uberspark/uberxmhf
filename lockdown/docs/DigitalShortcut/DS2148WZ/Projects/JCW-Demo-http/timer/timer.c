//
//  $Id: timer.c 60 2008-10-05 16:09:13Z jcw $
//  $Revision: 60 $
//  $Author: jcw $
//  $Date: 2008-10-05 12:09:13 -0400 (Sun, 05 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/timer/timer.c $
//

//
//  This timer code was contributed by Dave Madden
//

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#include "timer.h"

void timerInit (void)
{
  SCB_PCONP |= SCB_PCONP_PCTIM1;
}

void timerBeepOn (unsigned int hz)
{
  //
  //  Reset timer 1, disabled
  //
  T1_TCR = T_TCR_CR;

  if (hz < 60 || hz > 20000) 
    return;

  //
  //  Connect MAT1.0 and MAT1.1 to the speaker
  //
  PCB_PINSEL0 = ((PCB_PINSEL0 & ~(PCB_PINSEL0_P012_MASK | PCB_PINSEL0_P013_MASK)) | (PCB_PINSEL0_P012_MAT10 | PCB_PINSEL0_P013_MAT11));

  //
  //  Don't waste your time like I did: you can set the current
  //  states of MATx.x bits in the EMR register.  You don't have to
  //  use the SET and CLEAR actions to get the bits in the state you
  //  want, and then set to TOGGLE.  Aargh!
  //
  T1_EMR = T_EMR_EM0 | T_EMR_EMC0_TOGGLE | T_EMR_EMC1_TOGGLE;
  T1_MCR = T_MCR_MR2R;

  //
  //  Set MR0/MAT1.0 and MR1/MAT1.1 to toggle at the beginning of
  //  every half-cycle.  MR2 causes the timer to reset at the end of
  //  the half cycle.  The result is toggling at the frequency you
  //  want.
  //
  T1_MR0 = 1;
  T1_MR1 = 2;
  T1_MR2 = configCPU_CLOCK_HZ / hz / 2;

  T1_TCR = T_TCR_CE;
}

void timerBeepOff (void)
{
  T1_TCR = T_TCR_CR;

  //
  // Return P0.12 and P0.13 to GPIO inputs
  //
  PCB_PINSEL0 = ((PCB_PINSEL0 & ~(PCB_PINSEL0_P012_MASK | PCB_PINSEL0_P013_MASK)) | (PCB_PINSEL0_P012_GPIO | PCB_PINSEL0_P013_GPIO));

  GPIO0_IODIR &= ~(GPIO_IO_P12 | GPIO_IO_P13);
}

//
//  The timing on this has some variation since vTaskDelay() is relative, and
//  doesn't account for interrupts and other tasks.  Nonetheless, it
//  demonstrates a simple tune.
//
typedef struct note_s
{
  unsigned short int frequency;
  unsigned short int ms;
}
note_t;

static void timerBeepTune (const note_t *notes, unsigned int numberOfNotes)
{
  unsigned int i;

  for (i = 0; i < numberOfNotes; i++, notes++)
  {
    if (notes->frequency)
      timerBeepOn (notes->frequency);

    vTaskDelay (notes->ms / portTICK_RATE_MS);
  }

  timerBeepOff ();
}

void timerBeepMHALL (void)
{
  static const note_t maryHadALittleLamb [] = 
  {
    { 330,  375 }, { 294,  125 }, { 262,  250 }, { 294,  250 }, { 330,  250 }, { 330,  250 },
    { 330,  500 }, { 294,  250 }, { 294,  250 }, { 294,  500 }, { 330,  250 }, { 392,  250 },
    { 392,  500 }, { 330,  375 }, { 294,  125 }, { 262,  250 }, { 294,  250 }, { 330,  250 },
    { 330,  250 }, { 330,  250 }, { 330,  250 }, { 294,  250 }, { 294,  250 }, { 330,  250 },
    { 294,  250 }, { 262, 1000 }
  };

  timerBeepTune (maryHadALittleLamb, arrsizeof (maryHadALittleLamb));
}

void timerBeepSMOTW (void)
{
  static const note_t smokeOnTheWater [] = 
  {
    { 392, 1000 / 2}, { 440, 1000 / 2}, { 495, 1000 / 2}, {   0,  200 / 1},
    { 392, 1000 / 2}, { 440, 1000 / 2}, {   0,   50 / 1}, { 524,  500 / 2},
    { 495, 1000 / 2}, {   0,  200 / 1}, { 392, 1000 / 2}, { 440, 1000 / 2},
    { 495, 1000 / 2}, {   0,  200 / 1}, { 392,  500 / 2}, {   0,  100 / 1},
    { 392, 2000 / 2} 
  };

  timerBeepTune (smokeOnTheWater, arrsizeof (smokeOnTheWater));
}
