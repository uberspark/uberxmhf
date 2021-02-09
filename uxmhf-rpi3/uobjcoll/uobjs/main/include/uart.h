/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
	generic uart interface 
	will end up using either minuart or pl011 uart based on build configuration

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __UART_H__
#define __UART_H__

#define __ENABLE_UART__
#define __UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__

#if defined (__ENABLE_UART__)

	#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__)
		#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/pl011uart.h>
	#elif defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_MINI__)
		#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/miniuart.h>
	#else

	#endif

#endif


#ifndef __ASSEMBLY__

#if defined (__ENABLE_UART__)

	#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__)
		#define uart_init bcm2837_pl011uart_init
		#define uart_can_send bcm2837_pl011uart_can_send
		#define uart_can_recv bcm2837_pl011uart_can_recv
		#define uart_getc bcm2837_pl011uart_getc
		#define uart_putc bcm2837_pl011uart_putc
		#define uart_puts bcm2837_pl011uart_puts
		#define uart_flush bcm2837_pl011uart_flush
	#else
		#define uart_init bcm2837_miniuart_init
		#define uart_can_send bcm2837_miniuart_can_send
		#define uart_can_recv bcm2837_miniuart_can_recv
		#define uart_getc bcm2837_miniuart_getc
		#define uart_putc bcm2837_miniuart_putc
		#define uart_puts bcm2837_miniuart_puts
		#define uart_flush bcm2837_miniuart_flush
	#endif

#else

	#define uart_init(x) 
	#define uart_can_send(x)	1
	#define uart_can_recv(x)	1
	#define uart_getc(x)	1
	#define uart_putc(x)
	#define uart_puts(x)
	#define uart_flush(x)

#endif



#endif // __ASSEMBLY__



#endif //__UART_H__
