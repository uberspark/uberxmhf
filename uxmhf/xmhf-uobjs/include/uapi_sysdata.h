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
 *  sysdata (E820) state uAPI
 *
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __UAPI_SYSDATA_H__
#define __UAPI_SYSDATA_H__


#define UXMHF_UAPI_SYSDATA_E820ADDENTRY			1
#define UXMHF_UAPI_SYSDATA_E820GETMAXINDEX		2
#define UXMHF_UAPI_SYSDATA_E820GETENTRYFORINDEX	3


#ifndef __ASSEMBLY__

typedef struct {
	uint32_t baseaddr_low;
	uint32_t baseaddr_high;
	uint32_t length_low;
	uint32_t length_high;
	uint32_t type;
}__attribute__((packed)) uxmhf_uapi_sysdata_e820addentry_t;


typedef struct {
	uint32_t index;
}__attribute__((packed)) uxmhf_uapi_sysdata_e820getmaxindex_t;

typedef struct {
	uint32_t index;
	uint32_t baseaddr_low;
	uint32_t baseaddr_high;
	uint32_t length_low;
	uint32_t length_high;
	uint32_t type;
}__attribute__((packed)) uxmhf_uapi_sysdata_e820getentryforindex_t;


/*@
	requires \valid(e820entryp);
@*/
void usysd_e820addentry(uxmhf_uapi_sysdata_e820addentry_t *e820entryp);

/*@
	requires \valid(gentryp);
@*/
void usysd_e820getentryforindex(uxmhf_uapi_sysdata_e820getentryforindex_t *gentryp);

/*@
	requires \valid(indexp);
@*/
void usysd_e820getmaxindex(uxmhf_uapi_sysdata_e820getmaxindex_t *indexp);

extern __attribute__((section(".data"))) GRUBE820 usysd_memmapinfo[MAX_E820_ENTRIES];

extern __attribute__((section(".data"))) uint32_t usysd_memmapinfo_maxindex;



#endif	//__ASSEMBLY__

#endif //__UAPI_SYSDATA_H__
