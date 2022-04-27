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

#define FIO0DIR0	*(volatile unsigned char *)0x3FFFC000
#define FIO0DIR1	*(volatile unsigned char *)0x3FFFC001
#define FIO0DIR2	*(volatile unsigned char *)0x3FFFC002
#define FIO0DIR3	*(volatile unsigned char *)0x3FFFC003
#define FIO0DIRL	*(volatile unsigned short *)0x3FFFC000
#define FIO0DIRU	*(volatile unsigned short *)0x3FFFC002

#define FIO0MASK0	*(volatile unsigned char *)0x3FFFC010
#define FIO0MASK1	*(volatile unsigned char *)0x3FFFC011
#define FIO0MASK2	*(volatile unsigned char *)0x3FFFC012
#define FIO0MASK3	*(volatile unsigned char *)0x3FFFC013
#define FIO0MASKL	*(volatile unsigned short *)0x3FFFC010
#define FIO0MASKU	*(volatile unsigned short *)0x3FFFC012

#define FIO0PIN0	*(volatile unsigned char *)0x3FFFC014
#define FIO0PIN1	*(volatile unsigned char *)0x3FFFC015
#define FIO0PIN2	*(volatile unsigned char *)0x3FFFC016
#define FIO0PIN3	*(volatile unsigned char *)0x3FFFC017
#define FIO0PINL	*(volatile unsigned short *)0x3FFFC014
#define FIO0PINU	*(volatile unsigned short *)0x3FFFC016

#define FIO0SET0	*(volatile unsigned char *)0x3FFFC018
#define FIO0SET1	*(volatile unsigned char *)0x3FFFC019
#define FIO0SET2	*(volatile unsigned char *)0x3FFFC01A
#define FIO0SET3	*(volatile unsigned char *)0x3FFFC01B
#define FIO0SETL	*(volatile unsigned short *)0x3FFFC018
#define FIO0SETU	*(volatile unsigned short *)0x3FFFC01A

#define FIO0CLR0	*(volatile unsigned char *)0x3FFFC01C
#define FIO0CLR1	*(volatile unsigned char *)0x3FFFC01D
#define FIO0CLR2	*(volatile unsigned char *)0x3FFFC01E
#define FIO0CLR3	*(volatile unsigned char *)0x3FFFC01F
#define FIO0CLRL	*(volatile unsigned short *)0x3FFFC01C
#define FIO0CLRU	*(volatile unsigned short *)0x3FFFC01E


#define FIO1DIR		*(volatile unsigned int *)0x3FFFC020
#define FIO1MASK	*(volatile unsigned int *)0x3FFFC030
#define FIO1PIN		*(volatile unsigned int *)0x3FFFC034
#define FIO1SET		*(volatile unsigned int *)0x3FFFC038
#define FIO1CLR		*(volatile unsigned int *)0x3FFFC03C

#define FIO1DIR0	*(volatile unsigned char *)0x3FFFC020
#define FIO1DIR1	*(volatile unsigned char *)0x3FFFC021
#define FIO1DIR2	*(volatile unsigned char *)0x3FFFC022
#define FIO1DIR3	*(volatile unsigned char *)0x3FFFC023
#define FIO1DIRL	*(volatile unsigned short *)0x3FFFC020
#define FIO1DIRU	*(volatile unsigned short *)0x3FFFC022

#define FIO1MASK0	*(volatile unsigned char *)0x3FFFC030
#define FIO1MASK1	*(volatile unsigned char *)0x3FFFC031
#define FIO1MASK2	*(volatile unsigned char *)0x3FFFC032
#define FIO1MASK3	*(volatile unsigned char *)0x3FFFC033
#define FIO1MASKL	*(volatile unsigned short *)0x3FFFC030
#define FIO1MASKU	*(volatile unsigned short *)0x3FFFC032

#define FIO1PIN0	*(volatile unsigned char *)0x3FFFC034
#define FIO1PIN1	*(volatile unsigned char *)0x3FFFC035
#define FIO1PIN2	*(volatile unsigned char *)0x3FFFC036
#define FIO1PIN3	*(volatile unsigned char *)0x3FFFC037
#define FIO1PINL	*(volatile unsigned short *)0x3FFFC034
#define FIO1PINU	*(volatile unsigned short *)0x3FFFC036

#define FIO1SET0	*(volatile unsigned char *)0x3FFFC038
#define FIO1SET1	*(volatile unsigned char *)0x3FFFC039
#define FIO1SET2	*(volatile unsigned char *)0x3FFFC03A
#define FIO1SET3	*(volatile unsigned char *)0x3FFFC03B
#define FIO1SETL	*(volatile unsigned short *)0x3FFFC038
#define FIO1SETU	*(volatile unsigned short *)0x3FFFC03A

#define FIO1CLR0	*(volatile unsigned char *)0x3FFFC03C
#define FIO1CLR1	*(volatile unsigned char *)0x3FFFC03D
#define FIO1CLR2	*(volatile unsigned char *)0x3FFFC03E
#define FIO1CLR3	*(volatile unsigned char *)0x3FFFC03F
#define FIO1CLRL	*(volatile unsigned short *)0x3FFFC03C
#define FIO1CLRU	*(volatile unsigned short *)0x3FFFC03E


// Pin Connect Block Registers
typedef struct
{
  REG32 sel0;                           // Pin Function Select Register 0
  REG32 sel1;                           // Pin Function Select Register 1
  REG32 _pad[3];
  REG32 sel2;                           // Pin Function Select Register 2
} pinRegs_t;


#endif
