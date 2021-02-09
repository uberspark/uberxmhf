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
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/miniuart.h>
//#include <uberspark/include/uberspark.h>


extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);


/* mini UART functions */
void bcm2837_miniuart_init(void){
    unsigned int gpio_fnsel, i;

    mmio_write32(AUX_ENABLES,1);
    mmio_write32(AUX_MU_IER_REG,0);		//clear interrupt enable
    mmio_write32(AUX_MU_CNTL_REG,0);
    mmio_write32(AUX_MU_LCR_REG,3);
    mmio_write32(AUX_MU_MCR_REG,0);
    mmio_write32(AUX_MU_IER_REG,0);
    mmio_write32(AUX_MU_IIR_REG,0xC6);
    mmio_write32(AUX_MU_BAUD_REG,270); //((250,000,000/115200)/8)-1 = 270

    gpio_fnsel=mmio_read32(GPFSEL1);
    gpio_fnsel &= ~(7<<12); //GPIO 14 (TX)
    gpio_fnsel |= 2<<12;    //GPIO 14 -- Alternate Function 5
    gpio_fnsel &= ~(7<<15); //GPIO 15 (RX)
    gpio_fnsel |= 2<<15;    //GPIO 15 -- Alternate Function 5
    mmio_write32(GPFSEL1,gpio_fnsel);

    mmio_write32(GPPUD,0);
    for(i=0; i<150; i++);
    mmio_write32(GPPUDCLK0,(1<<14)|(1<<15));
    for(i=0; i<150; i++);
    mmio_write32(GPPUDCLK0,0);
    mmio_write32(AUX_MU_CNTL_REG,3);
}


bool bcm2837_miniuart_can_send(void){
    if (! (mmio_read32(AUX_MU_LSR_REG) & 0x20) )
        return false;
    else
        return true;
}

bool bcm2837_miniuart_can_recv(void){
	if( mmio_read32(AUX_MU_LSR_REG) & 0x01 ) 
        return true;
    else
        return false;
}


void bcm2837_miniuart_putc(u8 ch){
    while( bcm2837_miniuart_can_send() == false );
    mmio_write32(AUX_MU_IO_REG,(u32)ch);
}

void bcm2837_miniuart_puts(char *buffer){
	while (*buffer)
		bcm2837_miniuart_putc(*buffer++);
}


// UART character read function (non-blocking)
// return true if character read; false if no characters to read
bool bcm2837_miniuart_getc(u8 *recv_ch) {

    //do we have a character to receive?
	if( bcm2837_miniuart_can_recv() ) {
        
        //yes, so store the character
        *recv_ch=(u8)(mmio_read32(AUX_MU_IO_REG) & 0xFF);

        return true;   
    }else{
        return false;
    }

}


void bcm2837_miniuart_flush(void){
    while( (mmio_read32(AUX_MU_LSR_REG) & 0x100) );
}


