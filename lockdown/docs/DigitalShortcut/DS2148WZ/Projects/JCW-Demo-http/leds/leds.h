//
//  $Id: leds.h 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/leds/leds.h $
//

#ifndef _LEDS_H_
#define _LEDS_H_

#include "semphr.h"

//
//
//
extern xQueueHandle xLEDQueue;

//
//
//
portTASK_FUNCTION (vLEDFlashTask, pvParameters __attribute__ ((unused)));

#endif
