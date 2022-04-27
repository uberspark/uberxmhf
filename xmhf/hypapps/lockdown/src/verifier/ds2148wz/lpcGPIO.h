/*-
 ******************************************************************************
 *
 * $RCSfile: $
 * $Revision: $
 *
 * Header file for Philips LPC ARM Processors.
 * Copyright 2004 R O SoftWare
 *
 * No guarantees, warrantees, or promises, implied or otherwise.
 * May be used for hobby or commercial purposes provided copyright
 * notice remains intact.
 *
 *****************************************************************************/
#ifndef INC_LPC_GPIO_H
#define INC_LPC_GPIO_H

// General Purpose Input/Output Registers (GPIO)
typedef struct
{
  REG32 in0;                            // P0 Pin Value Register
  REG32 set0;                           // P0 Pin Output Set Register
  REG32 dir0;                           // P0 Pin Direction Register
  REG32 clr0;                           // P0 Pin Output Clear Register
  REG32 in1;                            // P1 Pin Value Register
  REG32 set1;                           // P1 Pin Output Set Register
  REG32 dir1;                           // P1 Pin Direction Register
  REG32 clr1;                           // P1 Pin Output Clear Register
  REG32 in2;                            // P2 Pin Value Register
  REG32 set2;                           // P2 Pin Output Set Register
  REG32 dir2;                           // P2 Pin Direction Register
  REG32 clr2;                           // P2 Pin Output Clear Register
  REG32 in3;                            // P3 Pin Value Register
  REG32 set3;                           // P3 Pin Output Set Register
  REG32 dir3;                           // P3 Pin Direction Register
  REG32 clr3;                           // P3 Pin Output Clear Register
} gpioRegs_t;


#define FIO0DIR		*(volatile unsigned int *)0x3FFFC000
#define FIO0MASK	*(volatile unsigned int *)0x3FFFC010
#define FIO0PIN		*(volatile unsigned int *)0x3FFFC014
#define FIO0SET		*(volatile unsigned int *)0x3FFFC018
#define FIO0CLR		*(volatile unsigned int *)0x3FFFC01C

#define FIO1DIR		*(volatile unsigned int *)0x3FFFC020
#define FIO1MASK	*(volatile unsigned int *)0x3FFFC030
#define FIO1PIN		*(volatile unsigned int *)0x3FFFC034
#define FIO1SET		*(volatile unsigned int *)0x3FFFC038
#define FIO1CLR		*(volatile unsigned int *)0x3FFFC03C

#define FIO1PINL	*(volatile unsigned int *)0x3FFFC034
#define FIO1PINU	*(volatile unsigned int *)0x3FFFC036
#define FIO1SETL	*(volatile unsigned int *)0x3FFFC038
#define FIO1SETU	*(volatile unsigned int *)0x3FFFC03A
#define FIO1CLRL	*(volatile unsigned int *)0x3FFFC03C
#define FIO1CLRU	*(volatile unsigned int *)0x3FFFC03E


// Pin Connect Block Registers
typedef struct
{
  REG32 sel0;                           // Pin Function Select Register 0
  REG32 sel1;                           // Pin Function Select Register 1
  REG32 _pad[3];
  REG32 sel2;                           // Pin Function Select Register 2
} pinRegs_t;


#endif
