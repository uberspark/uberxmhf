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


/*
 *
 *  I/O permission tables uAPI
 *
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __UAPI_IOTBL_H__
#define __UAPI_IOTBL_H__


#define UXMHF_UAPI_IOTBL_TEST					1
#define UXMHF_UAPI_IOTBL_GETIOTBLBASE			2
#define UXMHF_UAPI_IOTBL_INITIOTBL				3
#define UXMHF_UAPI_IOTBL_SETUPIOTBLUGPORTACCESS	4
#define UXMHF_UAPI_IOTBL_SETUPIOTBLUHPORTACCESS	5


#ifndef __ASSEMBLY__

extern uint8_t uiotbl_uhslab_iobitmap[XMHFGEEC_TOTAL_UHSLABS][3*PAGE_SIZE_4K];
extern uint8_t uiotbl_ugslab_iobitmap[XMHFGEEC_TOTAL_UGSLABS][3*PAGE_SIZE_4K];


typedef struct {
    uint32_t dst_slabid;
	uint32_t iotbl_base;
}__attribute__((packed)) uapi_iotbl_getiotblbase_t;


void uiotbl_getiotblbase(uapi_iotbl_getiotblbase_t *ps);


typedef struct {
    uint32_t dst_slabid;
}__attribute__((packed)) uapi_iotbl_initiotbl_t;


void uiotbl_initiotbl(uapi_iotbl_initiotbl_t *ps);

typedef struct {
	uint32_t ugslabiobitmap_idx;
	uint16_t port;
	uint16_t port_size;
}__attribute__((packed)) uapi_iotbl_setupiotblugportaccess_t;

void uiotbl_setupiotblugportaccess(uapi_iotbl_setupiotblugportaccess_t *ps);


typedef struct {
	uint32_t uhslabiobitmap_idx;
	uint16_t port;
	uint16_t port_size;
}__attribute__((packed)) uapi_iotbl_setupiotbluhportaccess_t;

void uiotbl_setupiotbluhportaccess(uapi_iotbl_setupiotbluhportaccess_t *ps);


/*@
	requires 0 <= uhslabiobitmap_idx < XMHFGEEC_TOTAL_UHSLABS;
	requires 0 <= port < 65536;
	requires 0 <= port_size <= 4;
@*/
void uiotbl_setupiotbluh_allowaccesstoport(uint32_t uhslabiobitmap_idx, uint16_t port, uint16_t port_size);


/*@
	requires 0 <= ugslabiobitmap_idx < XMHFGEEC_TOTAL_UGSLABS;
	requires 0 <= port < 65536;
	requires 0 <= port_size <= 4;
@*/
void uiotbl_setupiotblug_allowaccesstoport(uint32_t ugslabiobitmap_idx, uint16_t port, uint16_t port_size);


#endif	//__ASSEMBLY__

#endif //__UAPI_IOTBL_H__
