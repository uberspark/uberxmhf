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
	broadcom 2837 mailbox support

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __MAILBOX_H__
#define __MAILBOX_H__

#define MAILBOX_REQUEST    		0

//channels 
#define MAILBOX_CHANNEL_POWER   0
#define MAILBOX_CHANNEL_FB      1
#define MAILBOX_CHANNEL_VUART   2
#define MAILBOX_CHANNEL_VCHIQ   3
#define MAILBOX_CHANNEL_LEDS    4
#define MAILBOX_CHANNEL_BTNS    5
#define MAILBOX_CHANNEL_TOUCH   6
#define MAILBOX_CHANNEL_COUNT   7
#define MAILBOX_CHANNEL_PROP    8

// tags 
#define MAILBOX_TAG_GETSERIAL   0x10004
#define MAILBOX_TAG_SETCLKRATE  0x38002
#define MAILBOX_TAG_LAST        0

#ifndef __ASSEMBLY__

// make a mailbox call
// return: 0 if failure, non-zero on success
int bcm2837_mailbox_call(unsigned char channel, unsigned char *buffer, unsigned int buffer_size);


// mailbox return serial number
// return 0 on failure
u64 bcm2837_mailbox_get_board_serial(void);


#endif // __ASSEMBLY__



#endif //__MAILBOX_H__
