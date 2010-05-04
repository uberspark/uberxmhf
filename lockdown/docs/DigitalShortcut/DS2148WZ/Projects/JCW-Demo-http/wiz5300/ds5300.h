/** file ds5300.h
 * Digital Shortcut customized W5300 I/O fucntions for DS2148WZ board
 *
 * Copyright Digital Shortcut Inc. (BSD licence) 2009 **/
 
#ifndef	_DS5300_H_
#define	_DS5300_H_

#include "types.h"

void    setMR(uint16 val);
uint16  getMR(void);

void  	 iinchip_init(void);

uint16   IINCHIP_READ(uint32 addr);
void     IINCHIP_WRITE(uint32 addr,uint16 data);
uint32   wiz_write_buf(SOCKET s, uint8* buf,uint32 len);
uint32   wiz_read_buf(SOCKET s, uint8* buf,uint32 len);
void   	 wiz_write_test(uint16 addr, uint8* buf, int len);

void W5300PwrOn(void);
void W5300PwrOff(void);
void W5300IntInit(void);

int Rd5300_bl(uint16 addr, uint8* buf, int len);


#endif
