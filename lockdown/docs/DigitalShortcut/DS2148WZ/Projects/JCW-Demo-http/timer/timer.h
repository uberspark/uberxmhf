//
//  $Id: timer.h 60 2008-10-05 16:09:13Z jcw $
//  $Revision: 60 $
//  $Author: jcw $
//  $Date: 2008-10-05 12:09:13 -0400 (Sun, 05 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/timer/timer.h $
//

#ifndef _TIMER_H_
#define _TIMER_H_

//
//
//
void timerInit (void);
void timerBeepOn (unsigned int hz);
void timerBeepOff (void);
void timerBeepMHALL (void);
void timerBeepSMOTW (void);

#endif
