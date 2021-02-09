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
	broadcom 2837 mini uart support

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/mailbox.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/pl011uart.h>
//#include <uberspark/include/uberspark.h>


extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);


/* UART initialization function */
void bcm2837_pl011uart_init(void){
    register unsigned int r;
    unsigned int mbox_msg[9];
    unsigned int i;

    mmio_write32(PL011_UART_CR_REG, 0);         // turn off PL011 when we work with it
    
    // set up clock for consistent divisor values 
    mbox_msg[0] = sizeof(mbox_msg);
    mbox_msg[1] = MAILBOX_REQUEST;
    mbox_msg[2] = MAILBOX_TAG_SETCLKRATE; // set clock rate
    mbox_msg[3] = 12;
    mbox_msg[4] = 0;
    mbox_msg[5] = 2;           // UART clock
    mbox_msg[6] = 4000000;     // 4Mhz
    mbox_msg[7] = 0;           // clear turbo
    mbox_msg[8] = MAILBOX_TAG_LAST;

    bcm2837_mailbox_call(MAILBOX_CHANNEL_PROP, &mbox_msg, sizeof(mbox_msg));

    //map PL011 UART to GPIO pins
    r=mmio_read32(GPFSEL1);
    r &= ~((7<<12) | (7<<15)); // gpio14, gpio15
    r |= (4<<12) | (4<<15);    // alt0

#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011_CTSRTS__)
    r |= 0x00fc0000; 
#endif

    mmio_write32(GPFSEL1, r);


    mmio_write32(GPPUD, 0);            // remove current pullup/pulldown configuration

    for(i=0; i<150; i++);

#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011_CTSRTS__)
    mmio_write32(GPPUDCLK0, (1<<14)|(1<<15)|(1<<16)|(1<<17) );
#else
    mmio_write32(GPPUDCLK0, (1<<14)|(1<<15));
#endif

    for(i=0; i<150; i++);

    mmio_write32(GPPUD, 0);     // flush GPIO setup

    mmio_write32(GPPUDCLK0,0);  // flush GPIO setup


    mmio_write32(PL011_UART_ICR_REG, 0x7FF);    // clear interrupts
    mmio_write32(PL011_UART_IBRD_REG, 2);       // 115200 baud
    mmio_write32(PL011_UART_FBRD_REG, 0xB);
    mmio_write32(PL011_UART_LCR_REG, 0x0);      // flush transmit fifo
    
    for(i=0; i<150; i++);
    
//    mmio_write32(PL011_UART_LCR_REG, 0x72);  // 8 bits, odd parity, 1 stop bit, enable FIFO
    mmio_write32(PL011_UART_LCR_REG, 0x70);  // 8 bits, no parity, 1 stop bit, enable FIFO

#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011_CTSRTS__)
    mmio_write32(PL011_UART_CR_REG, 0xC301);     // enable CTS, RTS, Tx, Rx 
#else
    mmio_write32(PL011_UART_CR_REG, 0x301);     // enable Tx, Rx
#endif
}

bool bcm2837_pl011uart_can_send(void){
    if( (mmio_read32(PL011_UART_FR_REG) & 0x20) )
        return false;
    else   
        return true;
}

bool bcm2837_pl011uart_can_recv(void){
    if ( ! (mmio_read32(PL011_UART_FR_REG) & 0x10) )
        return true;
    else    
        return false;
}


/* UART character output function */
void bcm2837_pl011uart_putc(u8 ch){

    //wait until we can send 
    while( bcm2837_pl011uart_can_send() == false );
    mmio_write32(PL011_UART_DR_REG, ch);
}

/* UART string output function */
void bcm2837_pl011uart_puts(char *buffer){
	while (*buffer)
		bcm2837_pl011uart_putc(*buffer++);
}


// UART character read function (non-blocking)
// return true if character read; false if no characters to read
bool bcm2837_pl011uart_getc(u8 *recv_ch) {
    
    //check if there is a byte in the FIFO buffer
    if ( bcm2837_pl011uart_can_recv() ){

        //receive FIFO is not-empty, so read the next character
        *recv_ch=(u8)mmio_read32(PL011_UART_DR_REG);

        return true;
    }else{
        return false;
    }

}


/* UART flush */
void bcm2837_pl011uart_flush(void){
    while( !(mmio_read32(PL011_UART_FR_REG) & 0x80) );
}


