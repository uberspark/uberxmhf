//
//  $Id: sysdefs.h 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/sysdefs.h $
//

#ifndef _SYSDEFS_H_
#define _SYSDEFS_H_

#ifndef TRUE
#define TRUE (1)
#endif
#ifndef FALSE
#define FALSE (0)
#endif

typedef unsigned char U8;
typedef signed char N8;
typedef unsigned short U16;
typedef signed short N16;
typedef unsigned int U32;
typedef signed int N32;
typedef int BOOL;

typedef volatile U8 REG8;
typedef volatile U16 REG16;
typedef volatile U32 REG32;

#define pREG8  (REG8 *)
#define pREG16 (REG16 *)
#define pREG32 (REG32 *)

#ifndef NULL
#define NULL ((void *) 0)
#endif

#define MIN(x,y) ((x)<(y)?(x):(y))
#define MAX(x,y)((x)>(y)?(x):(y))
#define arrsizeof(x) ((sizeof (x))/(sizeof (x [0])))

//
//  Yuck.  Don't like this here, but what the heck...
//
#if !defined CFG_CONSOLE_USB && !defined CFG_CONSOLE_UART0 && !defined CFG_CONSOLE_UART1
#error "Must define CFG_CONSOLE_USB, CFG_CONSOLE_UART0 or CFG_CONSOLE_UART1"
#endif

#if defined CFG_CONSOLE_USB && (defined CFG_CONSOLE_UART0 || defined CFG_CONSOLE_UART1)
#error "Only one of CFG_CONSOLE_USB, CFG_CONSOLE_UART0 or CFG_CONSOLE_UART1 may be defined"
#endif
#if defined CFG_CONSOLE_UART0 && (defined CFG_CONSOLE_USB || defined CFG_CONSOLE_UART1)
#error "Only one of CFG_CONSOLE_USB, CFG_CONSOLE_UART0 or CFG_CONSOLE_UART1 may be defined"
#endif
#if defined CFG_CONSOLE_UART1 && (defined CFG_CONSOLE_USB || defined CFG_CONSOLE_UART0)
#error "Only one of CFG_CONSOLE_USB, CFG_CONSOLE_UART0 or CFG_CONSOLE_UART1 may be defined"
#endif

#endif
