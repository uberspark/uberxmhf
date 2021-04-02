/*-
 * Copyright (c) 1986, 1988, 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 * (c) UNIX System Laboratories, Inc.
 * All or some portions of this file are derived from material licensed
 * to the University of California by American Telephone and Telegraph
 * Co. or Unix System Laboratories, Inc. and are reproduced herein with
 * the permission of UNIX System Laboratories, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)subr_prf.c	8.3 (Berkeley) 1/21/94
 */

/*
 * debug api
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf.h>

#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_MEMORY__)

// Memory storing uberXMHF output. 1MB in size.
#define _LOG_MEM_SZ   (1*1024*1024)
__attribute__(( section(".data") )) __attribute__((aligned(4096))) char g_log_mem[_LOG_MEM_SZ];
static uint32_t _log_mem_pos = 0;

static void _dbgprint_logmem_addr(void){
  _XDPRINTF_("\nLog memory address:%#X\n", (unsigned long)g_log_mem);
}

#endif


#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__)

// default config parameters for serial port
uart_config_t g_uart_config = {115200,
							   8,
							   PARITY_NONE,
							   1,
							   0,
							   UART_CLOCKFREQ,
							   __UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_PORT__};

//low-level UART character output
void dbg_x86_uart_putc_bare(char ch){
  //wait for xmit hold register to be empty
  while ( ! (uberspark_uobjrtl_hw__generic_x86_32_intel__inb(g_uart_config.port+0x5) & 0x20) );

  //write the character
  uberspark_uobjrtl_hw__generic_x86_32_intel__outb((uint8_t)ch, g_uart_config.port);

  //wait for xmit hold register to be empty and line is idle
  while ( ! (uberspark_uobjrtl_hw__generic_x86_32_intel__inb(g_uart_config.port+0x5) & 0x40) );

  return;
}


// write character to serial port, translating '\n' to '\r\n'
void dbg_x86_uart_putc(char ch){
  if (ch == '\n') {
    dbg_x86_uart_putc_bare('\r');
  }
  dbg_x86_uart_putc_bare(ch);
}


// write string to serial port
//void dbg_x86_uart_putstr(const char *s){
//	while (*s)
//		dbg_x86_uart_putc(*s++);
//}

void xmhfhw_platform_serial_puts(char *buffer){
	while (*buffer)
		dbg_x86_uart_putc(*buffer++);
	/*while (*buffer){
        if(*buffer == '\n')
            dbg_x86_uart_putc_bare((uint32_t)'\r');

        dbg_x86_uart_putc_bare((uint32_t)*buffer);

        buffer++;
	}*/
}


//initialize UART comms.
//void dbg_x86_uart_init(char *params){
void xmhfhw_platform_serial_init(char *params){

  //override default UART parameters with the one passed via the
  //command line (if any)
  if(params){
    uberspark_uobjrtl_crt__memcpy((void *)&g_uart_config, (unsigned char const *)params, sizeof(uart_config_t));
  }

  // FIXME: work-around for issue #143
  g_uart_config.fifo = 0;

  // disable UART interrupts
  uberspark_uobjrtl_hw__generic_x86_32_intel__outb((uint8_t)0, g_uart_config.port+0x1); //clear interrupt enable register

  //disable FIFO
  uberspark_uobjrtl_hw__generic_x86_32_intel__outb((uint8_t)0, g_uart_config.port+0x2); //fifo disable


  //compute divisor latch data from baud-rate and set baud-rate
  {
	uint16_t divisor_latch_data = g_uart_config.clock_hz / (g_uart_config.baud * 16);

	uberspark_uobjrtl_hw__generic_x86_32_intel__outb(0x80, g_uart_config.port+0x3); //enable divisor latch access by
									    //writing to line control register

	uberspark_uobjrtl_hw__generic_x86_32_intel__outb((uint8_t)divisor_latch_data, g_uart_config.port); //write low 8-bits of divisor latch data
	uberspark_uobjrtl_hw__generic_x86_32_intel__outb((uint8_t)(divisor_latch_data >> 8), g_uart_config.port+0x1); //write high 8-bits of divisor latch data

   }

  //set data bits, stop bits and parity info. by writing to
  //line control register
  uberspark_uobjrtl_hw__generic_x86_32_intel__outb((uint8_t)((g_uart_config.data_bits - 5) |
               ((g_uart_config.stop_bits - 1) << 2) |
                      g_uart_config.parity), g_uart_config.port+0x3);

  //signal ready by setting DTR and RTS high in
  //modem control register
  uberspark_uobjrtl_hw__generic_x86_32_intel__outb((uint8_t)0x3, g_uart_config.port+0x4);

  return;
}
#endif

#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__) || defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_MEMORY__)

void uberspark_uobjrtl_debug__init(char *params){

  #if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__)
    xmhfhw_platform_serial_init(params);
  #endif

  #if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_MEMORY__)
    _log_mem_pos = 0;
    _dbgprint_logmem_addr();
  #endif
}

void dbgprintf (const char *fmt, ...){
    va_list       ap;
	int retval;
	char buffer[1024];
  int str_len = 0;

	va_start(ap, fmt);
	retval = vsnprintf((char *)&buffer, 1024, (const char *)fmt, ap);
	uberspark_uobjrtl_hw__generic_x86_32_intel__spin_lock(&libxmhfdebug_lock);

  #if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__)
	  xmhfhw_platform_serial_puts((char *)&buffer);
  #endif

  #if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_MEMORY__)
    str_len = uberspark_uobjrtl_crt__strlen(buffer);
    if(str_len > 0 && _log_mem_pos + str_len < _LOG_MEM_SZ){
      uberspark_uobjrtl_crt__memcpy(&g_log_mem[_log_mem_pos], buffer, str_len);
      _log_mem_pos += str_len;
    } // Discard subsequent logs if the memory is full
  #endif
	uberspark_uobjrtl_hw__generic_x86_32_intel__spin_unlock(&libxmhfdebug_lock);
    va_end(ap);
}

#else

void uberspark_uobjrtl_debug__init(char *params){
	(void)params;
}


#endif // defined
