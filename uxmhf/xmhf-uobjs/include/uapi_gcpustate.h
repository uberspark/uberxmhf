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
 *  guest cpu state uAPI
 *
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __UAPI_GCPUSTATE_H__
#define __UAPI_GCPUSTATE_H__


#define XMHF_HIC_UAPI_CPUSTATE_VMREAD           0
#define XMHF_HIC_UAPI_CPUSTATE_VMWRITE          1
#define XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD    2
#define XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE   3
#define XMHFGEEC_UAPI_CPUSTATE_GUESTMSRREAD	4
#define XMHFGEEC_UAPI_CPUSTATE_GUESTMSRWRITE	5




#define GCPUSTATE_MSR_LBR_SELECT		0

#define GCPUSTATE_MSR_LASTBRANCH_TOS		1

#define GCPUSTATE_MSR_IA32_DEBUGCTL		2

#define GCPUSTATE_MSR_LASTBRANCH_0_FROM_IP	3
#define GCPUSTATE_MSR_LASTBRANCH_1_FROM_IP	4
#define GCPUSTATE_MSR_LASTBRANCH_2_FROM_IP	5
#define GCPUSTATE_MSR_LASTBRANCH_3_FROM_IP	6
#define GCPUSTATE_MSR_LASTBRANCH_4_FROM_IP	7
#define GCPUSTATE_MSR_LASTBRANCH_5_FROM_IP	8
#define GCPUSTATE_MSR_LASTBRANCH_6_FROM_IP	9
#define GCPUSTATE_MSR_LASTBRANCH_7_FROM_IP	10
#define GCPUSTATE_MSR_LASTBRANCH_8_FROM_IP	11
#define GCPUSTATE_MSR_LASTBRANCH_9_FROM_IP	12
#define GCPUSTATE_MSR_LASTBRANCH_10_FROM_IP	13
#define GCPUSTATE_MSR_LASTBRANCH_11_FROM_IP	14
#define GCPUSTATE_MSR_LASTBRANCH_12_FROM_IP	15
#define GCPUSTATE_MSR_LASTBRANCH_13_FROM_IP	16
#define GCPUSTATE_MSR_LASTBRANCH_14_FROM_IP	17
#define GCPUSTATE_MSR_LASTBRANCH_15_FROM_IP	18


#define GCPUSTATE_MSR_LASTBRANCH_0_TO_IP	19
#define GCPUSTATE_MSR_LASTBRANCH_1_TO_IP	20
#define GCPUSTATE_MSR_LASTBRANCH_2_TO_IP	21
#define GCPUSTATE_MSR_LASTBRANCH_3_TO_IP	22
#define GCPUSTATE_MSR_LASTBRANCH_4_TO_IP	23
#define GCPUSTATE_MSR_LASTBRANCH_5_TO_IP	24
#define GCPUSTATE_MSR_LASTBRANCH_6_TO_IP	25
#define GCPUSTATE_MSR_LASTBRANCH_7_TO_IP	26
#define GCPUSTATE_MSR_LASTBRANCH_8_TO_IP	27
#define GCPUSTATE_MSR_LASTBRANCH_9_TO_IP	28
#define GCPUSTATE_MSR_LASTBRANCH_10_TO_IP	29
#define GCPUSTATE_MSR_LASTBRANCH_11_TO_IP	30
#define GCPUSTATE_MSR_LASTBRANCH_12_TO_IP	31
#define GCPUSTATE_MSR_LASTBRANCH_13_TO_IP	32
#define GCPUSTATE_MSR_LASTBRANCH_14_TO_IP	33
#define GCPUSTATE_MSR_LASTBRANCH_15_TO_IP	34

#define GCPUSTATE_MSR_TOTAL			35

#define GCPUSTATE_MSR_MAXCOUNT			128

#ifndef __ASSEMBLY__


typedef struct {
    uint64_t encoding;
    uint64_t value;
}__attribute__((packed)) xmhf_uapi_gcpustate_vmrw_params_t;

typedef struct {
    uint32_t msr;
    uint64_t value;
}__attribute__((packed)) xmhf_uapi_gcpustate_msrrw_params_t;


typedef struct {
    x86regs_t gprs;
}__attribute__((packed)) xmhf_uapi_gcpustate_gprs_params_t;


extern __attribute__((section(".data"))) x86regs_t guestgprs[MAX_PLATFORM_CPUS];
extern __attribute__((section(".data"))) uint64_t guestmsrs[GCPUSTATE_MSR_MAXCOUNT];


/*@
	requires \valid(vmrwp);
@*/
void ugcpust_vmread(xmhf_uapi_gcpustate_vmrw_params_t *vmrwp);

/*@
	requires \valid(vmrwp);
@*/
void ugcpust_vmwrite(uint32_t srcslabid, xmhf_uapi_gcpustate_vmrw_params_t *vmrwp);

/*@
	requires \valid(gprs);
	requires 0 <= cpuid < MAX_PLATFORM_CPUS;
@*/
void ugcpust_gprsread(uint32_t cpuid, xmhf_uapi_gcpustate_gprs_params_t *gprs);

/*@
	requires \valid(gprs);
	requires 0 <= cpuid < MAX_PLATFORM_CPUS;
@*/
void ugcpust_gprswrite(uint32_t cpuid, xmhf_uapi_gcpustate_gprs_params_t *gprs);

/*@
	requires \valid(msrrwp);
@*/
void ugcpust_msrread(xmhf_uapi_gcpustate_msrrw_params_t *msrrwp);

/*@
	requires \valid(msrrwp);
@*/
void ugcpust_msrwrite(xmhf_uapi_gcpustate_msrrw_params_t *msrrwp);



#endif	//__ASSEMBLY__

#endif //__UAPI_GCPUSTATE_H__
