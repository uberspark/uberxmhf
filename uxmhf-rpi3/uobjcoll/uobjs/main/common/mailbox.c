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
	broadcom 2837 mailbox implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/mailbox.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>
//#include <uberspark/include/uberspark.h>

//mailbox message buffer
//has to be aligned on a 16 byte boundary
__attribute__((aligned(16))) __attribute__((section(".data"))) volatile  unsigned int mailbox_msgbuf[MAILBOX_MAXBUFSIZE];

// make a mailbox call
// return: 0 if failure, non-zero on success
int bcm2837_mailbox_call(unsigned char channel, unsigned char *buffer, unsigned int buffer_size){
    unsigned int mailbox_msgbuf_channel_addr;
    int i;

    // sanity check buffer size
    if (buffer_size > MAILBOX_MAXBUFSIZE)
        return 0;

    //first copy the buffer into our mailbox message buffer
    uberspark_uobjrtl_crt__memcpy(mailbox_msgbuf, buffer, buffer_size);

    //compute address of the message buffer including the channel identifier
    mailbox_msgbuf_channel_addr = (((unsigned int)((unsigned long)&mailbox_msgbuf) & ~0xF) | ( channel &0xF ));
    
    // wait till we are clear to write to the mailbox
    do {
        for(i=0; i<5; i++); // nop
    } while ( mmio_read32(MAILBOX_STATUS_REG) & MAILBOX_FULL);

    //write the address of the message to the mailbox with channel identifier
    mmio_write32(MAILBOX_WRITE_REG, mailbox_msgbuf_channel_addr);

    //now wait for the response
    while(1) {
        // check for a reaponse
        do{
            for(i=0; i<5; i++); // nop
        }while ( mmio_read32(MAILBOX_STATUS_REG) & MAILBOX_EMPTY);
    
        // is it a response to our message?
        if(  mmio_read32(MAILBOX_READ_REG) == mailbox_msgbuf_channel_addr){
            // return 0 or non-zero based on if it isa valid successful response
            if( mailbox_msgbuf[1] == MAILBOX_RESPONSE){
                //copy mailbox message buffer into user buffer
                uberspark_uobjrtl_crt__memcpy(buffer, mailbox_msgbuf, buffer_size);
            }
            return (mailbox_msgbuf[1] == MAILBOX_RESPONSE);
        }
            
    }

    //we never get here
 	_XDPRINTF_("%s[%u]\n", __func__, __LINE__);
    return 0;
}

// mailbox return serial number
// return 0 on failure
u64 bcm2837_mailbox_get_board_serial(void){
    u64 board_serial=0;
    unsigned int mailbox_msg[8];
    
    // get the board's unique serial number with a mailbox call
    mailbox_msg[0] = sizeof(mailbox_msg);       // length of the message in bytes
    mailbox_msg[1] = MAILBOX_REQUEST;           // this is a request message
    mailbox_msg[2] = MAILBOX_TAG_GETSERIAL;     // get serial number command
    mailbox_msg[3] = 8;                         // output buffer size in bytes
    mailbox_msg[4] = 0;                         // 
    mailbox_msg[5] = 0;                         // clear output buffer
    mailbox_msg[6] = 0;
    mailbox_msg[7] = MAILBOX_TAG_LAST;

    if ( bcm2837_mailbox_call(MAILBOX_CHANNEL_PROP, &mailbox_msg, sizeof(mailbox_msg)) ){
        board_serial = ((u64)mailbox_msg[6] << 32) | (u64)mailbox_msg[5]; 
    }

    return (board_serial);
}


