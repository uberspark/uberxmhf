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

// XMHF core API -- x86vmx arch. backend
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcapi.h>
#include <xcihub.h>




///////////////////////////////////////////////////////////////////////////////
// Trapmask related APIs

 __attribute__((aligned(4096))) static xc_partition_trapmaskdata_x86vmx_t _trapmask_data[MAX_PRIMARY_PARTITIONS];

static void _trapmask_operation_trap_io_set(context_desc_t context_desc, xc_hypapp_arch_param_x86vmx_trapio_t trapio){
	u8 *bit_vector = (u8 *)_trapmask_data[context_desc.partition_desc.partition_index].vmx_iobitmap_region;
	u32 byte_offset, bit_offset;
	u32 i;

	if(trapio.access_size > sizeof(u32))
		trapio.access_size=sizeof(u32);

	for(i=0; i < trapio.access_size; i++){
		byte_offset = (trapio.portnum+i) / 8;
		bit_offset = (trapio.portnum+i) % 8;
		bit_vector[byte_offset] |= (1 << bit_offset);
	}
}

static void _trapmask_operation_trap_io_clear(context_desc_t context_desc, xc_hypapp_arch_param_x86vmx_trapio_t trapio){
	u8 *bit_vector = (u8 *)_trapmask_data[context_desc.partition_desc.partition_index].vmx_iobitmap_region;
	u32 byte_offset, bit_offset;
	u32 i;

	if(trapio.access_size > sizeof(u32))
		trapio.access_size=sizeof(u32);

	for(i=0; i < trapio.access_size; i++){
		byte_offset = (trapio.portnum+i) / 8;
		bit_offset = (trapio.portnum+i) % 8;
		bit_vector[byte_offset] &= ~((1 << bit_offset));
	}
}

void xc_api_trapmask_arch_set(context_desc_t context_desc, xc_hypapp_arch_param_t ap){
	switch(ap.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO:{
				_trapmask_operation_trap_io_set(context_desc, ap.param.trapio);
				break;
		}

		default:
			break;
	}

}

void xc_api_trapmask_arch_clear(context_desc_t context_desc, xc_hypapp_arch_param_t ap){
	switch(ap.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO:{
				_trapmask_operation_trap_io_clear(context_desc, ap.param.trapio);
				break;
		}

		default:
			break;
	}

}

u64 xc_api_trapmask_arch_gettrapmaskbuffer(context_desc_t context_desc, u64 operation){
    u64 retval=0;

    switch(operation){
        case XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO:
            retval = (u64)&_trapmask_data[context_desc.partition_desc.partition_index].vmx_iobitmap_region;
            break;

        default:
            break;
    }

    return retval;
}










