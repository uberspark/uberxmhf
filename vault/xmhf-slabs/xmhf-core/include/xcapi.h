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
 *  XMHF core API
 *
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __XCAPI_H__
#define __XCAPI_H__




#include <xcapihpt.h>
#include <xcapicpustate.h>
#include <xcapitrapmask.h>
#include <xcapipartition.h>
#include <xcapiplatform.h>

#ifndef __ASSEMBLY__


#define XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT						1
#define XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT_SIZE					(sizeof(context_desc_t)+sizeof(u64)+sizeof(u32))

#define XMHF_SLAB_XCAPI_FNXCAPIHPTGETPROT						2
#define XMHF_SLAB_XCAPI_FNXCAPIHPTGETPROT_SIZE					(sizeof(context_desc_t)+sizeof(u64))

#define XMHF_SLAB_XCAPI_FNXCAPIHPTSETENTRY						3
#define XMHF_SLAB_XCAPI_FNXCAPIHPTSETENTRY_SIZE					(sizeof(context_desc_t)+sizeof(u64)+sizeof(u64))

#define XMHF_SLAB_XCAPI_FNXCAPIHPTGETENTRY						4
#define XMHF_SLAB_XCAPI_FNXCAPIHPTGETENTRY_SIZE					(sizeof(context_desc_t)+sizeof(u64))

#define XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES					5
#define XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES_SIZE				(sizeof(context_desc_t))

#define XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHESSMP				6
#define XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHESSMP_SIZE			(sizeof(context_desc_t))

#define XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK					7
#define XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK_SIZE				(sizeof(context_desc_t)+sizeof(u64))

#define XMHF_SLAB_XCAPI_FNXCAPITRAPMASKSET						8
#define XMHF_SLAB_XCAPI_FNXCAPITRAPMASKSET_SIZE					(sizeof(context_desc_t)+sizeof(xc_hypapp_arch_param_t))

#define XMHF_SLAB_XCAPI_FNXCAPITRAPMASKCLEAR					9
#define XMHF_SLAB_XCAPI_FNXCAPITRAPMASKCLEAR_SIZE				(sizeof(context_desc_t)+sizeof(xc_hypapp_arch_param_t))

#define XMHF_SLAB_XCAPI_FNXCAPICPUSTATESET						10
#define XMHF_SLAB_XCAPI_FNXCAPICPUSTATESET_SIZE					(sizeof(context_desc_t)+sizeof(xc_hypapp_arch_param_t))

#define XMHF_SLAB_XCAPI_FNXCAPICPUSTATEGET						11
#define XMHF_SLAB_XCAPI_FNXCAPICPUSTATEGET_SIZE					(sizeof(context_desc_t)+sizeof(u64))

#define XMHF_SLAB_XCAPI_FNXCAPIPARTITIONCREATE					12
#define XMHF_SLAB_XCAPI_FNXCAPIPARTITIONCREATE_SIZE				(sizeof(u32))

#define XMHF_SLAB_XCAPI_FNXCAPIPARTITIONADDCPU					13
#define XMHF_SLAB_XCAPI_FNXCAPIPARTITIONADDCPU_SIZE				(sizeof(u32)+sizeof(u32)+sizeof(bool))

#define XMHF_SLAB_XCAPI_FNXCAPIPARTITIONGETCONTEXTDESC			14
#define XMHF_SLAB_XCAPI_FNXCAPIPARTITIONGETCONTEXTDESC_SIZE		(sizeof(u32))

#define XMHF_SLAB_XCAPI_FNXCAPIPARTITIONSTARTCPU				15
#define XMHF_SLAB_XCAPI_FNXCAPIPARTITIONSTARTCPU_SIZE			(sizeof(context_desc_t))

#define XMHF_SLAB_XCAPI_FNXCAPIPLATFORMSHUTDOWN					16
#define XMHF_SLAB_XCAPI_FNXCAPIPLATFORMSHUTDOWN_SIZE			(sizeof(context_desc_t))

#define	XMHF_SLAB_XCAPI_FNXCCOREAPIARCHEVENTHANDLERNMIEXCEPTION			17
#define	XMHF_SLAB_XCAPI_FNXCCOREAPIARCHEVENTHANDLERNMIEXCEPTION_SIZE 	(0)














#endif	//__ASSEMBLY__


#endif //__XCAPI_H__
