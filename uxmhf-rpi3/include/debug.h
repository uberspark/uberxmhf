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
	debug module definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __DEBUG_H__
#define __DEBUG_H__

#ifndef __ASSEMBLY__


#if defined (__DEBUG_UART__)



extern __attribute__(( section(".data") )) u32 xdprintfsmp_lock;

static inline void _XDPRINTF_(const char *fmt, ...){
    va_list       ap;
	int retval;
	char buffer[1024];

	va_start(ap, fmt);
	retval = vsnprintf(&buffer, 1024, fmt, ap);
	//spin_lock(&libxmhfdebug_lock);
	uart_puts(&buffer);
	uart_flush();
	//spin_unlock(&libxmhfdebug_lock);
    va_end(ap);
}


static inline void _XDPRINTFSMP_(const char *fmt, ...){
    va_list       ap;
	int retval;
	char buffer[1024];

	va_start(ap, fmt);
	retval = vsnprintf(&buffer, 1024, fmt, ap);
	spin_lock(&xdprintfsmp_lock);
	uart_puts(&buffer);
	uart_flush();
	spin_unlock(&xdprintfsmp_lock);
    va_end(ap);
}

#else

#define _XDPRINTF_(format, args...)
#define _XDPRINTFSMP_(format, args...)

#endif // defined




void debug_hexdumpu32(u32 value);

#define HALT() while(1);

#endif // __ASSEMBLY__





#endif //__DEBUG_H__
