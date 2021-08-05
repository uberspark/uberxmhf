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
	picar_s test application

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __PICAR_S_H__
#define __PICAR_S_H__

#define UAPP_PICAR_S_FUNCTION_TEST	11
#define UAPP_PICAR_S_FUNCTION_PROT  12
#define UAPP_PICAR_S_FUNCTION_UNPROT 13

#ifndef __ASSEMBLY__

typedef struct {
	/* In parameters */
	uint32_t encrypted_buffer_va;
	uint32_t decrypted_buffer_va;
   uint32_t buffer_va;
	uint8_t len;
	uint32_t array;
	int speed;
	int turn_angle;
   int step;
	/* Out parameters */
	uint32_t out_speed;
	uint32_t out_turn_angle;
	uint32_t out_step;
}picar_s_param_t;

#endif // __ASSEMBLY__



#endif //__PICAR_S_H__
