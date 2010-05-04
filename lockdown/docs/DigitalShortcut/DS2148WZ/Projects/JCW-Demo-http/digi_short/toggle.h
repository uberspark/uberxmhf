/** file toggle.h
 * DS2148WZ Pin Toggle Header
 *
 * Rev 1.0 JD 3-10-2009
 * Copyright Digital Shortcut Inc. (BSD licence) 2009 **/

#ifndef _TOGGLE_
#define _TOGGLE_

portTASK_FUNCTION (vPinToggleTask, pvParameters __attribute__ ((unused)));
portTASK_FUNCTION (vPinToggDelTask, pvParameters __attribute__ ((unused)));
portTASK_FUNCTION (vPinSlowTask, pvParameters __attribute__ ((unused)));

#endif
