//
//  $Id: eintsISR.c 45 2008-10-05 03:19:52Z jcw $
//  $Revision: 45 $
//  $Author: jcw $
//  $Date: 2008-10-04 23:19:52 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/eints/eintsISR.c $
//

#include "FreeRTOS.h"
#include "task.h"

#include "eintsISR.h"

//
//
//
static void eintsISR_EINT0_Handler (void)
{
  SCB_EXTINT |= SCB_EXTINT_EINT0;

  GPIO0_FIOSET = GPIO_IO_P11;

	VIC_VectAddr = (unsigned portLONG) 0;
}

void eintsISR_EINT0 (void) __attribute__ ((naked));
void eintsISR_EINT0 (void)
{
  portSAVE_CONTEXT ();
  eintsISR_EINT0_Handler ();
  portRESTORE_CONTEXT ();
}

//
//
//
static void eintsISR_EINT2_Handler (void)
{
  SCB_EXTINT |= SCB_EXTINT_EINT1;

  GPIO0_FIOCLR = GPIO_IO_P11;

	VIC_VectAddr = (unsigned portLONG) 0;
}

void eintsISR_EINT2 (void) __attribute__ ((naked));
void eintsISR_EINT2 (void)
{
  portSAVE_CONTEXT ();
  eintsISR_EINT2_Handler ();
  portRESTORE_CONTEXT ();
}

