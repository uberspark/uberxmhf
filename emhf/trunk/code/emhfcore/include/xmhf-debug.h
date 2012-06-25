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

// EMHF secure loader component declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_DEBUG_H__
#define __EMHF_DEBUG_H__

//bring in arch. specific declarations
#include <arch/xmhf-debug-arch.h>

#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//exported DATA 
extern uint8_t g_log_targets;
extern uint8_t g_log_level;
//extern unsigned char g_dbg_ctype[];

//----------------------------------------------------------------------
//definitions
#define print_string putstr

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

#define _U	0x01	/* upper */
#define _L	0x02	/* lower */
#define _D	0x04	/* digit */
#define _C	0x08	/* cntrl */
#define _P	0x10	/* punct */
#define _S	0x20	/* white space (space/lf/tab) */
#define _X	0x40	/* hex digit */
#define _SP	0x80	/* hard space (0x20) */


/*#define __ismask(x) (g_dbg_ctype[(int)(unsigned char)(x)])

#define isalnum(c)	((__ismask(c)&(_U|_L|_D)) != 0)
#define isalpha(c)	((__ismask(c)&(_U|_L)) != 0)
#define iscntrl(c)	((__ismask(c)&(_C)) != 0)
#define isdigit(c)	((__ismask(c)&(_D)) != 0)
#define isgraph(c)	((__ismask(c)&(_P|_U|_L|_D)) != 0)
#define islower(c)	((__ismask(c)&(_L)) != 0)
#define isprint(c)	((__ismask(c)&(_P|_U|_L|_D|_SP)) != 0)
#define ispunct(c)	((__ismask(c)&(_P)) != 0)
#define isspace(c)	((__ismask(c)&(_S)) != 0)
#define isupper(c)	((__ismask(c)&(_U)) != 0)
#define isxdigit(c)	((__ismask(c)&(_D|_X)) != 0)

#define isascii(c) (((unsigned char)(c))<=0x7f)
#define toascii(c) (((unsigned char)(c))&0x7f)

static inline unsigned char __tolower(unsigned char c)
{
  int ctemp;
  if (isupper(c))
    ctemp -= 'A'-'a';
  return (unsigned char)ctemp;
}

static inline unsigned char __toupper(unsigned char c)
{
  int ctemp;
  if (islower(c))
    ctemp -= 'a'-'A';
  return (unsigned char)ctemp;
}

#define tolower(c) __tolower(c)
#define toupper(c) __toupper(c)
*/


//----------------------------------------------------------------------
//exported FUNCTIONS 
void emhf_debug_init(char *params);

#include <stdio.h>
#ifdef __DEBUG_SERIAL__
	/* void printf(const char *format, ...) */
	/*   __attribute__ ((format (printf, 1, 2))); */
	void dprintf(u32 log_type, const char *format, ...)
	  __attribute__ ((format (printf, 2, 3)));
	void dvprintf(u32 log_type, const char *fmt, va_list args);
	void print_hex(const char *prefix, const void *prtptr, size_t size);

#else
	/* #define printf(format, args...) while(0) */
	#define dprintf(format, args...) while(0)
	#define dvprintf(log_type, fmt, args) while(0)
	#define print_hex(prefix, prtptr, size) while(0)
#endif





#endif	//__ASSEMBLY__

#endif //__EMHF_DEBUG_H__
