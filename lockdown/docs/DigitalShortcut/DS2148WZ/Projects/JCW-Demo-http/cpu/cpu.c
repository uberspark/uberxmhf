//
//  $Id: cpu.c 53 2008-10-05 03:23:41Z jcw $
//  $Revision: 53 $
//  $Author: jcw $
//  $Date: 2008-10-04 23:23:41 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/cpu/cpu.c $
//

#include "FreeRTOS.h"

#include "../fiq/fiq.h"
#include "cpu.h"

//
//
//
typedef struct intVects_s
{
  unsigned int reset;
  unsigned int undefined;
  unsigned int swi;
  unsigned int pabt;
  unsigned int dabt;
  unsigned int reserved;
  unsigned int irq;
  unsigned int fiq;

  void *reset_handler;
  void *undefined_handler;
  void *swi_handler;
  void *pabt_handler;
  void *dabt_handler;
  void *reserved_handler;
  void *irq_handler;
  void *fiq_handler;
}
__attribute__ ((packed)) intVects_t;

//
//
//
extern unsigned int __intvects;

//
//  Olimex board specific.  LEDs are on P0.10, P0.11
//
#define partstFIRST_IO			  ((unsigned portLONG) 0x400)
#define partstNUM_LEDS			  (2)
#define partstALL_OUTPUTS_OFF	((unsigned portLONG) 0xffffffff)

//
//
//
void cpuSetupHardware (void)
{
#ifdef RUN_FROM_RAM
  //
  //  Remap the interrupt vectors to RAM if we are are running from RAM
  //
  SCB_MEMMAP = SCB_MEMMAP_URM;
#endif

  //
  //  Use fast I/O on both ports
  //
  SCB_SCS = SCB_SCS_GPIO0M | SCB_SCS_GPIO1M;

  //
  //  Configure pin functions.  Port 0 gets UART 0 & 1 set.  All other pins
  //  are set to GPIO, including the Debug port (P1.26) and the Trace port 
  //  (P1.25..P1.16).
  //
  PCB_PINSEL0 = (PCB_PINSEL0_P00_TXD0 | PCB_PINSEL0_P01_RXD0 | PCB_PINSEL0_P08_TXD1 | PCB_PINSEL0_P09_RXD1);
  PCB_PINSEL1 = 0;
  PCB_PINSEL2 = (PCB_PINSEL2_P13626_DEBUG | PCB_PINSEL2_P12516_GPIO);

  //
  //  Set all GPIO to output other than the P0.14 (BSL), and the JTAG pins.  
  //  The JTAG pins are left as input as I'm not sure what will happen if the 
  //  Wiggler is connected after powerup - not that it would be a good idea to
  //  do that anyway.
  //
  GPIO0_FIODIR = ~(GPIO_IO_P14 | GPIO_IO_P15 | GPIO_IO_P15);
  GPIO1_FIODIR = ~GPIO_IO_JTAG;

  //
  //  Setup the PLL to multiply the 12Mhz XTAL input by 5, divide by 1
  //
  SCB_PLLCFG = (SCB_PLLCFG_MUL5 | SCB_PLLCFG_DIV1);

  //
  //  Activate the PLL by turning it on then feeding the correct sequence of bytes
  //
  SCB_PLLCON  = SCB_PLLCON_PLLE;
  SCB_PLLFEED = SCB_PLLFEED_FEED1;
  SCB_PLLFEED = SCB_PLLFEED_FEED2;

  //
  //  Wait for the PLL to lock...
  //
  while (!(SCB_PLLSTAT & SCB_PLLSTAT_PLOCK))
    ;

  //
  //  ...before connecting it using the feed sequence again
  //
  SCB_PLLCON  = SCB_PLLCON_PLLC | SCB_PLLCON_PLLE;
  SCB_PLLFEED = SCB_PLLFEED_FEED1;
  SCB_PLLFEED = SCB_PLLFEED_FEED2;

  //
  //  Setup and turn on the MAM.  Three cycle access is used due to the fast
  //  PLL used.  It is possible faster overall performance could be obtained by
  //  tuning the MAM and PLL settings.
  //
  MAM_TIM = MAM_TIM_3;
  MAM_CR = MAM_CR_FULL;

  //
  //  Setup the peripheral bus to be the same as the PLL output (48Mhz)
  //
  SCB_VPBDIV = SCB_VPBDIV_100;

  //
  //  Disable power to all modules
  //
  SCB_PCONP = 0x0000;

  //
  //  Make sure all interrupts disabled
  //
  VIC_IntEnClr = VIC_IntEnClr_MASK;

  //
  //  Put FIQ handler in RAM
  //
  fiqFIQISRCopyToRAM ();

  //
  //  Lastly, switch interrupt handlers to RAM vectors
  //
  SCB_MEMMAP = SCB_MEMMAP_URM;

  //
  //
  //
  cpuGPIOInitialize ();
}

//
//
//
void cpuSetupFIQISR (void *FIQInterrupt)
{
  intVects_t *ivRam = (intVects_t *) &__intvects;

  ivRam->fiq_handler = FIQInterrupt;
}

//
//
//
void cpuPLLDisable (void)
{
  SCB_PLLCON  = 0;
  SCB_PLLFEED = SCB_PLLFEED_FEED1;
  SCB_PLLFEED = SCB_PLLFEED_FEED2;
  SCB_PLLCFG =  0;
}

//
//
//
void cpuT1Disable (void)
{
  T1_TCR = 0;
  T1_PR = 0;
  T1_MCR = 0;
  T1_CCR = 0;
  T1_EMR = 0;
  T1_CTCR = 0;
  T1_IR = 0;
}

//
//
//
void cpuGPIOInitialize (void)
{
	GPIO0_FIOSET = partstALL_OUTPUTS_OFF;
}

//
//
//
void cpuToggleLED (unsigned portBASE_TYPE uxLED)
{
  unsigned portLONG ulLED = partstFIRST_IO;

  if (uxLED < partstNUM_LEDS)
  {
    ulLED <<= (unsigned portLONG) uxLED;

    if (GPIO0_FIOPIN & ulLED)
      GPIO0_FIOCLR = ulLED;
    else
      GPIO0_FIOSET = ulLED;			
  }	
}
