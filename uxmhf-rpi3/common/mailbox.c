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

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <mailbox.h>

//mailbox message buffer
//has to be aligned on a 16 byte boundary
volatile __attribute__((aligned(16))) unsigned int mailbox_msgbuf[MAILBOX_MAXBUFSIZE];


// make a mailbox call
// return: 0 if failure, non-zero on success
int bcm2837_mailbox_call(unsigned char channel, unsigned char *buffer, unsigned int buffer_size){
    unsigned int mailbox_msgbuf_channel_addr;
    int i;

    // sanity check buffer size
    if (buffer_size > MAILBOX_MAXBUFSIZE)
        return 0;

    //first copy the buffer into our mailbox message buffer
    memcpy(mailbox_msgbuf, buffer, buffer_size);

    //compute address of the message buffer including the channel identifier
    mailbox_msgbuf_channel_addr = (((unsigned int)((unsigned long)&mailbox_msgbuf) & ~0xF) | ( channel &0xF ));
    
    // wait till we are clear to write to the mailbox
    do {
        for(i=0; i<5; i++); // nop
    } while (*((volatile unsigned int *)MAILBOX_STATUS_REG) & MAILBOX_FULL);

    //write the address of the message to the mailbox with channel identifier
    *((volatile unsigned int *)MAILBOX_WRITE_REG) = mailbox_msgbuf_channel_addr;

    //now wait for the response
    while(1) {
        // check for a reaponse
        do{
            for(i=0; i<5; i++); // nop
        }while (*((volatile unsigned int *)MAILBOX_STATUS_REG) & MAILBOX_EMPTY);
    
        // is it a response to our message?
        if(  *((volatile unsigned int *)MAILBOX_READ_REG) == mailbox_msgbuf_channel_addr){
            // return 0 or non-zero based on if it isa valid successful response
            return (mailbox_msgbuf[1] == MAILBOX_RESPONSE);
        }
            
    }

    //we never get here
    return 0;
}
