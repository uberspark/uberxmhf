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
 * EMHF partition component interface
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf-core.h>

//initialize partition monitor for a given CPU
//void xmhf_partition_initializemonitor(VCPU *vcpu){
//	xmhf_partition_arch_initializemonitor(vcpu);
//}
//void xmhf_partition_initializemonitor(context_desc_t context_desc){
//	xmhf_partition_arch_initializemonitor(context_desc);
//}
void xmhf_partition_initializemonitor(u32 index_cpudata){
	xmhf_partition_arch_initializemonitor(index_cpudata);
}


//setup guest OS state for the partition
//void xmhf_partition_setupguestOSstate(VCPU *vcpu){
//	xmhf_partition_arch_setupguestOSstate(vcpu);
//}
//void xmhf_partition_setupguestOSstate(context_desc_t context_desc){
//	xmhf_partition_arch_setupguestOSstate(context_desc);
//}
void xmhf_partition_setupguestOSstate(u32 index_cpudata){
	xmhf_partition_arch_setupguestOSstate(index_cpudata);
}


//start executing the partition and guest OS
//void xmhf_partition_start(VCPU *vcpu){
//	xmhf_partition_arch_start(vcpu);
//}
//void xmhf_partition_start(context_desc_t context_desc){
//	xmhf_partition_arch_start(context_desc);
//}
void xmhf_partition_start(u32 index_cpudata){
	xmhf_partition_arch_start(index_cpudata);
}


//set legacy I/O protection for the partition
void xmhf_partition_legacyIO_setprot(context_desc_t context_desc, u32 port, u32 size, u32 prottype){
	xmhf_partition_arch_legacyIO_setprot(context_desc, port, size, prottype);
}
