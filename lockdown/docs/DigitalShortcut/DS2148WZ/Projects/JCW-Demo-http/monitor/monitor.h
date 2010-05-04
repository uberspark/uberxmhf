//
//  $Id: monitor.h 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/monitor/monitor.h $
//

#ifndef _MONITOR_H_
#define _MONITOR_H_

#include "FreeRTOS.h"
#include "task.h"

//
//
//
typedef enum
{
  CMDTYPE_CMDLIST = 0,
  CMDTYPE_FUNCTION
}
cmdType_e;

//
//
//
typedef struct commandList_s
{
  const portCHAR *command;
  portCHAR minArgs;
  portCHAR maxArgs;
  cmdType_e cmdType;
  union
  {
    const void *trickGCC;
    int (*handler) (int argc, portCHAR **argv);
    struct commandList_s *commandList;
  };
  const portCHAR *description;
  const portCHAR *parameters;
}
commandList_t;

//
//
//
portTASK_FUNCTION_PROTO (vMonitorTask, pvParameters);

#endif
