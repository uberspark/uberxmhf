#ifndef _NETIF_TYPE_H_
#define _NETIF_TYPE_H_
/**
 * \file    types.h
 * Type Definition of Variables.
 *
 * The simple data types supported by the W5300 programs are used to define function return values,
 * function and message parameters, and structure members.
 * They define the size and meaning of these elements.
 *
 */


typedef char int8;                        /**< The 8-bit signed data type. */

typedef volatile char vint8;              /**< The volatile 8-bit signed data type. */
                                           
typedef unsigned char uint8;              /**< The 8-bit unsigned data type. */
                                           
typedef volatile unsigned char vuint8;    /**< The volatile 8-bit unsigned data type. */
                                           
typedef short int16;                      /**< The 16-bit signed data type. */
                                           
typedef volatile short vint16;            /**< The volatile 16-bit signed data type. */
                                           
typedef unsigned short uint16;            /**< The 16-bit unsigned data type. */
                                           
typedef volatile unsigned short vuint16;  /**< The volatile 16-bit unsigned data type. */
                                           
typedef long int32;                       /**< The 32-bit signed data type. */
                                           
typedef volatile long vint32;             /**< The volatile 32-bit signed data type. */
                                           
typedef unsigned long uint32;             /**< The 32-bit unsigned data type. */
                                           
typedef volatile unsigned long vuint32;   /**< The volatile 32-bit unsigned data type. */

#define	_ENDIAN_LITTLE_	0	/**<  This must be defined if system is little-endian alignment */
#define	_ENDIAN_BIG_		1

// ARM7 LPC2148 is configured as Little Endian Device
#define 	SYSTEM_ENDIAN		_ENDIAN_LITTLE_

/**
 * The SOCKET data type.
 */
typedef uint8 SOCKET;


typedef unsigned long	ulong;
typedef unsigned short	ushort;
typedef unsigned char	uchar;
typedef unsigned int    uint;

//typedef uint8			u_char;		/**< 8-bit value */
//typedef uint8 			SOCKET;
//typedef uint16			u_short;	/**< 16-bit value */
//typedef uint16			u_int;		/**< 16-bit value */
//typedef uint32			u_long;		/**< 32-bit value */

typedef union _un_l2cval {
	ulong		lVal;
	uint8		cVal[4];
}un_l2cval;

typedef union _un_i2cval {
	uint16	iVal;
	uint8		cVal[2];
}un_i2cval;

// ?????
//#define TX_RX_MAX_BUF_SIZE	2048
//#define TX_BUF	0x1100
//#define RX_BUF	(TX_BUF+TX_RX_MAX_BUF_SIZE)


#ifndef __cplusplus
typedef int				bool;
#define	true			1
#define false			0
#endif

// print in hex value.
// type= 8 : print in format "ff".
// type=16 : print in format "ffff".
// type=32 : print in format "ffffffff".
typedef enum {
	VAR_LONG=32,
	VAR_SHORT=16,
	VAR_CHAR=8
} VAR_TYPE;

#ifndef NULL
#define NULL (void *)0
#endif

#endif		/* _NETIF_TYPE_H_ */
