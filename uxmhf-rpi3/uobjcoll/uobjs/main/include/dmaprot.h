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
	DMA protection module definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __DMAPROT_H__
#define __DMAPROT_H__


#ifndef __ASSEMBLY__

#define dmapa_to_syspa(x) (x & 0x3FFFFFFFUL)
#define syspa_to_dmapa(x) (x | 0xC0000000UL)

typedef struct {
	arm8_32_regs_t *r;
	u32 va;
	u32 pa;
	u32 sas;
	u32 srt;
	u32 wnr;
	u32 il;
} info_intercept_data_abort_t;


typedef struct {
	u32 ti;
	u32 src_addr;
	u32 dst_addr;
	u32 len;
	u32 stride;
	u32 next_cb_addr;
	u32 rsv_0;
	u32 rsv_1;
} dmac_cb_t;


void dmaprot_activate(void);

void dmaprot_handle_dmacontroller_access(info_intercept_data_abort_t *ida);

void dmaprot_handle_usbdmac_access(info_intercept_data_abort_t *ida);


#endif // __ASSEMBLY__



#endif //__DMAPROT_H__
