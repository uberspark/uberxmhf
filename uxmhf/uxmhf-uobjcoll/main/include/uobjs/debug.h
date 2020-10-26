/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

#ifndef __XMHF_DEBUG_H__
#define __XMHF_DEBUG_H__

#ifndef __ASSEMBLY__


#if defined (__DEBUG_SERIAL__)

//#include <xmhfhw.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geecgeecgeec_com.h>       		//UART/serial

#define LOG_LEVEL_NONE    0x00
#define LOG_LEVEL_ALL     0xFF

#define LOG_TARGET_NONE   0x00
#define LOG_TARGET_VGA    0x01
#define LOG_TARGET_SERIAL 0x02
#define LOG_TARGET_MEMORY 0x04

#define LOG_PROFILE (1<<0)
#define LOG_TRACE   (1<<1)
#define LOG_ERROR   (1<<2)

#define ENABLED_LOG_TYPES (LOG_PROFILE|LOG_TRACE|LOG_ERROR)

static inline void xmhf_debug_init(char *params){
	(void)params;
  xmhfhw_platform_serial_init(params);
}

extern __attribute__(( section(".data") )) uint32_t libxmhfdebug_lock;

static inline void _XDPRINTF_(const char *fmt, ...){
    va_list       ap;
	int retval;
	char buffer[1024];

	va_start(ap, fmt);
	retval = vsnprintf(&buffer, 1024, fmt, ap);
	spin_lock(&libxmhfdebug_lock);
	xmhfhw_platform_serial_puts(&buffer);
	spin_unlock(&libxmhfdebug_lock);
    va_end(ap);
}

#else

static inline void xmhf_debug_init(char *params){
	(void)params;
}

#define _XDPRINTF_(format, args...)

#endif // defined





#endif	//__ASSEMBLY__

#endif //__XMHF_DEBUG_H__
