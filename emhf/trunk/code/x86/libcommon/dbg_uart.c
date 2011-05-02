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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

/* uart.c: A simple transmit-only driver for 16550-series UARTs. 
 *   Hardwired to use COM0 (0x3f8)
 *   No interrupt support 
 * Useful for debugging using a remote serial console and for
 * displaying SecVisor messages.
 * Written by Arvind Seshadri
 */

#include <target.h>
#include <str.h>

#define PORT DEBUG_PORT

/* Register offsets */
#define RBR             0x00    /* receive buffer       */
#define THR             0x00    /* transmit holding     */
#define IER             0x01    /* interrupt enable     */
#define IIR             0x02    /* interrupt identity   */
#define FCR             0x02    /* FIFO control         */
#define LCR             0x03    /* line control         */
#define MCR             0x04    /* Modem control        */
#define LSR             0x05    /* line status          */
#define MSR             0x06    /* Modem status         */
#define DLL             0x00    /* divisor latch (lsb) (DLAB=1) */
#define DLH             0x01    /* divisor latch (msb) (DLAB=1) */

/* FIFO Control Register */
#define FCR_ENABLE      0x01    /* enable FIFO          */
#define FCR_CLRX        0x02    /* clear Rx FIFO        */
#define FCR_CLTX        0x04    /* clear Tx FIFO        */

/* Line Control Register */
#define LCR_DLAB        0x80    /* Divisor Latch Access */

/* Modem Control Register */
#define MCR_DTR         0x01    /* Data Terminal Ready  */
#define MCR_RTS         0x02    /* Request to Send      */
#define MCR_OUT2        0x08    /* OUT2: interrupt mask */
#define MCR_LOOP        0x10    /* Enable loopback test mode */

/* Line Status Register */
#define LSR_THRE        0x20    /* Xmit hold reg empty  */
#define LSR_TEMT        0x40    /* Xmitter empty        */

/* These parity settings can be ORed directly into the LCR. */
#define PARITY_NONE     (0<<3)
#define PARITY_ODD      (1<<3)
#define PARITY_EVEN     (3<<3)
#define PARITY_MARK     (5<<3)
#define PARITY_SPACE    (7<<3)

/* Frequency of external clock source. This definition assumes PC platform. */
#define UART_CLOCK_HZ   1843200

#define UART_READ_REG(x) \
    inb(PORT+(x));

#define UART_WRITE_REG(x, y)                        \
    outb((x), PORT+(y));

/* Config parameters for serial port */
static struct {
  u32 baud;
  u8 data_bits;
  u8 parity;
  u8 stop_bits;
  u8 fifo;
} uart_config = {115200, 8, PARITY_NONE, 1, 0};

/* LCR value macro (from tboot/common/early_printk.c) */
#define TARGET_LCR_VALUE(d, s, p) ((d - 5) | ((s - 1) << 2) | p)

#define TARGET_BAUD      115200
#define BAUD_AUTO ((unsigned int)(-1))

/* from tboot/common/early_printk.c */
typedef struct {
    unsigned short io_base;
    unsigned int   baud;
    unsigned int   clock_hz;
    unsigned char  lcr;
} tboot_serial_t;

/* from tboot/common/early_printk.c */
static tboot_serial_t g_serial_vals = {
    0x3f8,                              /* ttyS0 / COM1 */
    TARGET_BAUD,
    UART_CLOCK_HZ,
    TARGET_LCR_VALUE(8, 1, PARITY_NONE) /* default 8n1 LCR */
};


static int check_existence(void)
{
    unsigned char status; 

    /* Note really concerned with IER test */

    /*
     * Check to see if a UART is really there.
     * Use loopback test mode.
     */
    outb(MCR_LOOP | 0x0A, g_serial_vals.io_base + MCR);
    status = inb(g_serial_vals.io_base + MSR) & 0xF0;

    return (status == 0x90);
}

/* from tboot/common/early_printk.c */
/* 
 * serial config parsing support ported from xen drivers/char/ns16550.c
 * Copyright (c) 2003-2005, K A Fraser
 */
static unsigned char parse_parity_char(int c)
{
    switch ( c )
    {
    case 'n':
        return PARITY_NONE;
    case 'o': 
        return PARITY_ODD;
    case 'e': 
        return PARITY_EVEN;
    case 'm': 
        return PARITY_MARK;
    case 's': 
        return PARITY_SPACE;
    }
    return 0;
}

/* from tboot/common/early_printk.c */
static void early_serial_parse_port_config(const char *conf)
{
    unsigned char data_bits = 8, stop_bits = 1, parity;
    unsigned int baud;

    if ( strncmp(conf, "auto", 4) == 0 ) {
        g_serial_vals.baud = BAUD_AUTO;
        conf += 4;
    }
    else if ( (baud = (unsigned int)simple_strtoul(conf, &conf, 10))
              != 0 )
        g_serial_vals.baud = baud;

    if ( *conf == '/' ) {
        conf++;
        g_serial_vals.clock_hz = simple_strtoul(conf, &conf, 0) << 4;
    }

    if ( *conf != ',' )
        goto config_parsed;
    conf++;

    data_bits = (unsigned char)simple_strtoul(conf, &conf, 10);

    parity = parse_parity_char(*conf);
    if ( *conf != '\0' )
        conf++;

    stop_bits = (unsigned char)simple_strtoul(conf, &conf, 10);

    g_serial_vals.lcr = TARGET_LCR_VALUE(data_bits, stop_bits, parity);

    if ( *conf == ',' ) {
        conf++;
        g_serial_vals.io_base = (short)simple_strtoul(conf, &conf, 0);
        /* no irq, tboot not expecting Rx */
    }

config_parsed:
    /* Sanity checks - disable serial logging if input is invalid */
    if ( (g_serial_vals.baud != BAUD_AUTO) &&
         ((g_serial_vals.baud < 1200) || (g_serial_vals.baud > 115200)) )
        g_log_targets &= ~LOG_TARGET_SERIAL;
    if ( (data_bits < 5) || (data_bits > 8) )
        g_log_targets &= ~LOG_TARGET_SERIAL;
    if ( (stop_bits < 1) || (stop_bits > 2) )
        g_log_targets &= ~LOG_TARGET_SERIAL;
    if ( g_serial_vals.io_base == 0 )
        g_log_targets &= ~LOG_TARGET_SERIAL;
    if ( !check_existence() )
        g_log_targets &= ~LOG_TARGET_SERIAL;
}




//static
inline u32 uart_tx_empty(void)
{
  u8 x;
  x = UART_READ_REG(LSR)
  return (x & LSR_THRE);
}

#ifdef __DEBUG_SERIAL__
static void serial_putc(u32 x)
{

  while ( !uart_tx_empty() )
    ;
  UART_WRITE_REG((u8)x, THR);

  return;
}
#else
static void serial_putc(u32 x)
{
}
#endif

/* print a newline-containing null-terminated string to the serial port */
void putstr(const char *str)
{
  u8 tmp;

  while ((tmp = (u8)*str++) != '\0')
  {
    if (tmp == '\n')
        serial_putc('\r');        
        //tmp = '\r';
    serial_putc(tmp);
  }

  return;
}

void init_uart(void)
{
  u16 divisor;
  u8 x;

  /* write divisor latch to set baud rate */
  divisor = UART_CLOCK_HZ / (uart_config.baud * 16);
  UART_WRITE_REG(LCR_DLAB, LCR);
  UART_WRITE_REG((u8)divisor, DLL);
  UART_WRITE_REG((u8)(divisor >> 8), DLH);

  /* Disable all serial port interrupt sources */
  UART_WRITE_REG((u8)0, IER);

  /* Enable and clear Tx and Rx FIFOs */
  UART_WRITE_REG((u8)(FCR_ENABLE | FCR_CLRX | FCR_CLTX), FCR);

  /* Check if it a 16550 or higher UART. Otherwise we have no FIFOs */
  x = UART_READ_REG(IIR);
  if ( x == 0x0c)
    uart_config.fifo = 1;

  /* Set data format */
  UART_WRITE_REG((u8)((uart_config.data_bits - 5) | 
               ((uart_config.stop_bits - 1) << 2) |
                      uart_config.parity), LCR);

  /* Keep DTR and RTS high to keep remote happy */
  UART_WRITE_REG( MCR_DTR | MCR_RTS, MCR);

  return;
}
