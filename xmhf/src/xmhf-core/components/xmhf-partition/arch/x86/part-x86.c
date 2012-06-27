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
 * x86 backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//initialize partition monitor for a given CPU
void emhf_partition_arch_initializemonitor(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		emhf_partition_arch_x86svm_initializemonitor(vcpu);
	}else{ //CPU_VENDOR_INTEL
		emhf_partition_arch_x86vmx_initializemonitor(vcpu);
	}

}

//setup guest OS state for the partition
void emhf_partition_arch_setupguestOSstate(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		emhf_partition_arch_x86svm_setupguestOSstate(vcpu);
	}else{ //CPU_VENDOR_INTEL
		emhf_partition_arch_x86vmx_setupguestOSstate(vcpu);
	}
}

//start executing the partition and guest OS
void emhf_partition_arch_start(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		emhf_partition_arch_x86svm_start(vcpu);
	}else{ //CPU_VENDOR_INTEL
		emhf_partition_arch_x86vmx_start(vcpu);
	}
	
}

//set legacy I/O protection for the partition
void emhf_partition_arch_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype){
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		emhf_partition_arch_x86svm_legacyIO_setprot(vcpu, port, size, prottype);
	}else{ //CPU_VENDOR_INTEL
		emhf_partition_arch_x86vmx_legacyIO_setprot(vcpu, port, size, prottype);
	}
	
}
