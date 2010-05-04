/** file wiz_ds.h
 * WIZnet-Digital Shortcut stuff	
 * wiz_ds Header
 *
 * Copyright Digital Shortcut Inc. (BSD licence) 2009 **/

#ifndef _WIZDS_H_
#define _WIZDS_H_

#include "../wiz5300/types.h"

#define LATCH_STRB	(1 << 24)
#define WIZ_CS			(1 << 25)
#define WIZ_ON			(1 << 23)
#define WIZ_RES			(1 << 21)
#define WIZ_RD			(1 << 20)
#define WIZ_WR			(1 << 19)
#define WIZ_A0			(1 << 16)
#define WIZ_A1			(1 << 17)
#define WIZ_A2			(1 << 18)

#define LATCH_STRBa	(1 << 8)
#define WIZ_CSa			(1 << 9)
#define WIZ_ONa			(1 << 7)
#define WIZ_RESa		(1 << 5)
#define WIZ_RDa			(1 << 4)
#define WIZ_WRa			(1 << 3)

#define LATCH_STRBb	(1 << 0)
#define WIZ_CSb			(1 << 1)



void	W5300PwrOn(void);
void	W5300PwrOff(void);
void	W5300IntInit(void);

void	w5300Init(void);
void	WizNetInit(void);
void	ShowIPs(void);
void	ShowSSRs(void);
void	WizCheck0(void);
void	Dis5300Int(void);
void	En5300Int(void);

void	delay(unsigned long d);
void	LogIni(void);
void	LogWr( uint16 data );
void	LogWrTim( void );
void	LogDisplay( void );
char* itoa(unsigned int num, char* buf, int radix );

#endif
