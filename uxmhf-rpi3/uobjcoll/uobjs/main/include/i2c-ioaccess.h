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
	i2c_ioaccess application

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __I2C_IOACCESS_H__
#define __I2C_IOACCESS_H__

#define UAPP_I2C_IOACCESS_WRITEL  0x1000
#define UAPP_I2C_IOACCESS_READL  0x1001
#define UAPP_I2C_IOACCESS_HMAC  0x1002
#define UAPP_I2C_IOACCESS_READBUFFER  0x1003

#ifndef __ASSEMBLY__

bool uapp_i2c_ioaccess_handle_fast_hcall(arm8_32_regs_t *r);

typedef struct {
	uint32_t  in_buffer_va;
	uint32_t  out_buffer_va;
	uint8_t len;
}uapp_i2c_ioaccess_hmac_param_t;



#endif // __ASSEMBLY__


#endif //__I2C_IOACCESS_H__
