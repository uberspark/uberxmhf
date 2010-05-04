//
//  $Id: eints.c 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/eints/eints.c $
//

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#include "eints.h"
#include "eintsISR.h"

//
//
//
void eintsInit (void)
{
  portENTER_CRITICAL ();

  PCB_PINSEL1 |= PCB_PINSEL1_P016_EINT0;
  PCB_PINSEL0 |= PCB_PINSEL0_P015_EINT2;

  SCB_EXTPOLAR &= ~(SCB_EXTPOLAR_EINT0 | SCB_EXTPOLAR_EINT2);
  SCB_EXTMODE  |=  (SCB_EXTMODE_EINT0  | SCB_EXTMODE_EINT2);
  SCB_EXTINT   |=  (SCB_EXTINT_EINT0   | SCB_EXTINT_EINT2);

  VIC_IntSelect &= ~(VIC_IntSelect_EINT0 | VIC_IntSelect_EINT2);
  VIC_VectAddr4 = (portLONG) eintsISR_EINT0;
  VIC_VectCntl4 = VIC_VectCntl_ENABLE | VIC_Channel_EINT0;
  VIC_VectAddr5 = (portLONG) eintsISR_EINT2;
  VIC_VectCntl5 = VIC_VectCntl_ENABLE | VIC_Channel_EINT2;
  VIC_IntEnable = VIC_IntEnable_EINT0 | VIC_IntEnable_EINT2;

  portEXIT_CRITICAL ();
}
