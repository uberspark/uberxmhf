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

/*
 * low-level UART comms.
 * author: amit vasudevan (amitvasudevan@acm.org)
 */ 

#include <xmhf.h> 

// frequency of UART clock source
#define UART_CLOCKFREQ   1843200

// default config parameters for serial port 
uart_config_t g_uart_config = {115200, 
							   8, 
							   PARITY_NONE, 
							   1, 
							   0, 
							   UART_CLOCKFREQ, 
							   DEBUG_PORT};

//low-level UART character output
static void dbg_x86_uart_putc_bare(char ch){
  //wait for xmit hold register to be empty
  while ( ! (inb(g_uart_config.port+0x5) & 0x20) );
  
  //write the character
  outb((u8)ch, g_uart_config.port);

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
void dbg_x86_uart_putstr(const char *s){
	while (*s)
		dbg_x86_uart_putc(*s++);
}


//initialize UART comms.
void dbg_x86_uart_init(char *params){

  //override default UART parameters with the one passed via the
  //command line
  memcpy((void *)&g_uart_config, params, sizeof(uart_config_t));

  // FIXME: work-around for issue #143 
  g_uart_config.fifo = 0; 

  // disable UART interrupts
  outb((u8)0, g_uart_config.port+0x1); //clear interrupt enable register
  
  //compute divisor latch data from baud-rate and set baud-rate
  {
	u16 divisor_latch_data = g_uart_config.clock_hz / (g_uart_config.baud * 16);
  
	outb(0x80, g_uart_config.port+0x3); //enable divisor latch access by
									    //writing to line control register

	outb((u8)divisor_latch_data, g_uart_config.port); //write low 8-bits of divisor latch data
	outb((u8)(divisor_latch_data >> 8), g_uart_config.port+0x1); //write high 8-bits of divisor latch data 
	
   }
   
  //set data bits, stop bits and parity info. by writing to
  //line control register
  outb((u8)((g_uart_config.data_bits - 5) | 
               ((g_uart_config.stop_bits - 1) << 2) |
                      g_uart_config.parity), g_uart_config.port+0x3);

  //signal ready by setting DTR and RTS high in
  //modem control register
  outb((u8)0x3, g_uart_config.port+0x4);

  return;
}
