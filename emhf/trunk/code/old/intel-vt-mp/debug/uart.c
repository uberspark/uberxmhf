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

#define PORT 0x3f8

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

static inline u32 uart_tx_empty(void)
{
  u8 x;
  x = UART_READ_REG(LSR)
  return (x & LSR_THRE);
}

static void serial_putc(u32 x)
{

  while ( !uart_tx_empty() )
    ;
  UART_WRITE_REG((u8)x, THR);

  return;
}

/* print a newline-containing null-terminated string to the serial port */
void putstr(const char *str)
{
  u8 tmp;

  while ((tmp = (u8)*str++) != '\0')
  {
    if (tmp == '\n')
      tmp = '\r';
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
