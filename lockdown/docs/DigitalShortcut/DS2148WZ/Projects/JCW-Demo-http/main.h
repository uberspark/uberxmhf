//
//  $Id: main.h 63 2008-10-05 18:13:29Z jcw $
//  $Revision: 63 $
//  $Author: jcw $
//  $Date: 2008-10-05 14:13:29 -0400 (Sun, 05 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/main.h $
//

#ifndef _MAIN_H_
#define _MAIN_H_

//
//
//
#define __VERSION "1.30"

//
//
//
typedef enum
{
  TASKHANDLE_MONITOR = 0,
  TASKHANDLE_LED,
  TASKHANDLE_LCD,
  TASKHANDLE_TOGGLE,
  TASKHANDLE_UPDATEV,
  TASKHANDLE_SLOW,
  TASKHANDLE_TOGDEL,
  TASKHANDLE_MONOPOL,
  TASKHANDLE_HTTPSERV,
  TASKHANDLE_LAST
}
taskHandle_e;

extern xTaskHandle taskHandles [TASKHANDLE_LAST];

#endif
