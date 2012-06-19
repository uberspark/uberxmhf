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

// EMHF partition component 
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_PARTITION_H__
#define __EMHF_PARTITION_H__

//partition legacy I/O protection types
#define	PART_LEGACYIO_NOACCESS		(1)		//no access
#define	PART_LEGACYIO_READWRITE		(2)		//read and write access

//partition legacy I/O port sizes
#define PART_LEGACYIO_PORTSIZE_BYTE		(1)		//8-bit port
#define PART_LEGACYIO_PORTSIZE_WORD		(2)		//16-bit port
#define PART_LEGACYIO_PORTSIZE_DWORD	(4)		//32-bit port


#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//exported DATA 
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------

//initialize partition monitor for a given CPU
void emhf_partition_initializemonitor(VCPU *vcpu);

//setup guest OS state for the partition
void emhf_partition_setupguestOSstate(VCPU *vcpu);

//start executing the partition and guest OS
void emhf_partition_start(VCPU *vcpu);

//set legacy I/O protection for the partition
void emhf_partition_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype);


//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------
//initialize partition monitor for a given CPU
void emhf_partition_arch_initializemonitor(VCPU *vcpu);

//setup guest OS state for the partition
void emhf_partition_arch_setupguestOSstate(VCPU *vcpu);

//start executing the partition and guest OS
void emhf_partition_arch_start(VCPU *vcpu);

//set legacy I/O protection for the partition
void emhf_partition_arch_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype);


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
//initialize partition monitor for a given CPU
void emhf_partition_arch_x86vmx_initializemonitor(VCPU *vcpu);

//setup guest OS state for the partition
void emhf_partition_arch_x86vmx_setupguestOSstate(VCPU *vcpu);

//start executing the partition and guest OS
void emhf_partition_arch_x86vmx_start(VCPU *vcpu);

//low-level HVM start routine (part-x86vmx-sup.S)
u32 __vmx_start_hvm(void);

//set legacy I/O protection for the partition
void emhf_partition_arch_x86vmx_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype);


//----------------------------------------------------------------------
//x86svm SUBARCH. INTERFACES
//----------------------------------------------------------------------
//initialize partition monitor for a given CPU
void emhf_partition_arch_x86svm_initializemonitor(VCPU *vcpu);

//setup guest OS state for the partition
void emhf_partition_arch_x86svm_setupguestOSstate(VCPU *vcpu);

//start executing the partition and guest OS
void emhf_partition_arch_x86svm_start(VCPU *vcpu);

//low-level HVM start routine (part-x86svm-sup.S)
void __svm_start_hvm(VCPU *vcpu, u32 vmcb_paddr);

//set legacy I/O protection for the partition
void emhf_partition_arch_x86svm_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype);







#endif	//__ASSEMBLY__

#endif //__EMHF_PARTITION_H__
