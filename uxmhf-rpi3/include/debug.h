/*
	debug module definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __DEBUG_H__
#define __DEBUG_H__

#ifndef __ASSEMBLY__


#if defined (__DEBUG_SERIAL__)



extern __attribute__(( section(".data") )) u32 xdprintfsmp_lock;

static inline void _XDPRINTF_(const char *fmt, ...){
    va_list       ap;
	int retval;
	char buffer[1024];

	va_start(ap, fmt);
	retval = vsnprintf(&buffer, 1024, fmt, ap);
	//spin_lock(&libxmhfdebug_lock);
	bcm2837_miniuart_puts(&buffer);
	bcm2837_miniuart_flush();
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
	bcm2837_miniuart_puts(&buffer);
	bcm2837_miniuart_flush();
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
