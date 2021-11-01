#ifndef	_DS5300_H_
#define	_DS5300_H_
/**
 * \file    ds5300.h
 *    Customized W5300 I/O functions.
 *
 * This file defines the memory map and values of W5300 register.\n
 * Also, it defines the basic I/O function to access register of W5300. 
 *
 *
 */
 
#include "types.h"

void 		P1Init(void);
void    setMR(uint16 val);
uint16  getMR(void);
void  	iinchip_init(void);
uint16  IINCHIP_READ(uint32 addr);
void    IINCHIP_WRITE(uint32 addr,uint16 data);
uint32  wiz_write_buf(SOCKET s, uint8* buf,uint32 len);
uint32  wiz_read_buf(SOCKET s, uint8* buf,uint32 len);
void 		W5300PwrOn(void);
void 		W5300PwrOff(void);
void 		W5300Init2(void);
int 		Rd5300_bl(uint16 addr, uint8* buf, int len);

#endif
