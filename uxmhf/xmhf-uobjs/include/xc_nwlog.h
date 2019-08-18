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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

// XMHF core network logging
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XC_NWLOG_H__
#define __XC_NWLOG_H__

#define XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE 0
#define XMHFGEEC_SLAB_XC_NWLOG_LOGDATA	  1

#define E1000_TIMEOUT_1MS	((0x40000000ULL * 2) / 1000)


#ifndef __ASSEMBLY__




//////
// general types
/////

#define XC_NWLOG_BUF_MAXELEM	3
#define XC_NWLOG_BUF_MAXIDX	1

typedef struct {
    uint32_t logbuf[16];
}__attribute__((packed)) xcnwlog_ls_element_t;


typedef struct {
    uint8_t dst_mac[6];
    uint8_t src_mac[6];
    uint8_t type[2];
    uint8_t reserved[2];
	uint32_t logbuf[48];
}__attribute__((packed)) xcnwlog_packet_t;




//extern __attribute__((section(".slab_dmadata"))) xcnwlog_ls_element_t xcnwlog_lsdma[XC_NWLOG_BUF_MAXIDX][XC_NWLOG_BUF_MAXELEM];

extern __attribute__((section(".slab_dmadata"))) __attribute__((aligned(4096))) uint8_t xcnwlog_desc[PAGE_SIZE_4K];

extern __attribute__((section(".slab_dmadata"))) __attribute__((aligned(4096))) xcnwlog_packet_t xcnwlog_packet;


extern __attribute__((section(".data"))) xcnwlog_ls_element_t xcnwlog_ls[XC_NWLOG_BUF_MAXIDX][XC_NWLOG_BUF_MAXELEM];
extern __attribute__((section(".data"))) uint32_t xcnwlog_ls_index[XC_NWLOG_BUF_MAXIDX];


extern __attribute__((section(".data"))) char e1000_driver_name[];
extern __attribute__((section(".data"))) char e1000_driver_string[];
extern __attribute__((section(".data"))) char e1000_driver_version[];


extern __attribute__((section(".data"))) pci_device_t e1000_dev;
extern __attribute__((section(".data"))) struct e1000_adapter e1000_adapt;
extern __attribute__((section(".data"))) unsigned int e1000_irq;

//------------------------------------------------------------------------------
//[CONFIGURATION:START]
//this changes according to deployment platform
extern __attribute__((section(".data"))) unsigned char e1000_dst_macaddr[];
extern __attribute__((section(".data"))) unsigned char e1000_pkt_type[];



//@	logic uint32_t nwlogCapacity{L}(uint32_t nwlog_id) = (uint32_t)16;

//@	logic uint32_t nwlogSize{L}(uint32_t nwlog_id) = xcnwlog_ls_index[nwlog_id];

//@	logic xcnwlog_ls_element_t * nwlogStorage{L}(uint32_t nwlog_id) = &xcnwlog_ls[nwlog_id][0];

/*@
 predicate nwlogTop{L}(xcnwlog_ls_element_t * elem, integer index, xcnwlog_ls_element_t input) =
		(elem[index].logbuf[0] == input.logbuf[0] &&
		elem[index].logbuf[1] == input.logbuf[1] &&
		elem[index].logbuf[2] == input.logbuf[2] &&
		elem[index].logbuf[3] == input.logbuf[3] &&
		elem[index].logbuf[4] == input.logbuf[4]
		);
*/

//@	predicate nwlogEmpty{L}(uint32_t nwlog_id) = (nwlogSize(nwlog_id) == 0);

//@	predicate nwlogFull{L}(uint32_t nwlog_id) = (nwlogSize(nwlog_id) == nwlogCapacity(nwlog_id));

/*@
	predicate
	nwlogUnchanged {A,B } ( xcnwlog_ls_element_t * a, integer first, integer last ) =
	\forall integer i; first <= i < last
	==> ( (\at (a[i].logbuf[0] , A) == \at( a[i].logbuf[0] , B)) &&
		(\at (a[i].logbuf[1] , A) == \at( a[i].logbuf[1] , B)) &&
		(\at (a[i].logbuf[2] , A) == \at( a[i].logbuf[2] , B)) &&
		(\at (a[i].logbuf[3] , A) == \at( a[i].logbuf[3] , B)) &&
		(\at (a[i].logbuf[4] , A) == \at( a[i].logbuf[4] , B))
	);
*/

/*@
	predicate nwlogValid{L}(uint32_t nwlog_id) =
		(nwlog_id < XC_NWLOG_BUF_MAXIDX &&
		0 < nwlogCapacity( nwlog_id) &&
		0 <= nwlogSize (nwlog_id) <= nwlogCapacity ( nwlog_id) &&
		\valid (nwlogStorage (nwlog_id) + (0 .. nwlogCapacity (nwlog_id) - 1))
		);
@*/


uint32_t e1000_init_module(void);
void e1000_xmitack(void);

void xcnwlog_ls_push(uint32_t nwlog_id, xcnwlog_ls_element_t elem);
void xcnwlog_init(void);
void xcnwlog_logdata(xcnwlog_ls_element_t elem);



#endif //__ASSEMBLY__


#endif //__XC_NWLOG_H__
