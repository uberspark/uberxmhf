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

// Advanced Configuration and Power-management Interface (ACPI) definitions
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __LOCKDOWN_ACPI_H__
#define __LOCKDOWN_ACPI_H__

#ifndef __ASSEMBLY__

extern u64 __PM1a_STS, __PM1a_EN, __PM1b_STS, __PM1b_EN;
extern u64 __PM1_CNTa, __PM1_CNTb;
extern u32 __PM1a_STS_size, __PM1a_EN_size, __PM1b_STS_size, __PM1b_EN_size;
extern u32 __PM1_CNTa_size, __PM1_CNTb_size;

#define PM1a_STS			__PM1a_STS
#define PM1a_STS_SIZE	__PM1a_STS_size
#define PM1a_EN				__PM1a_EN
#define PM1a_EN_SIZE	__PM1a_EN_size
#define PM1b_STS			__PM1b_STS
#define PM1b_STS_SIZE	__PM1b_STS_size
#define PM1b_EN				__PM1b_EN
#define PM1b_EN_SIZE	__PM1b_EN_size
#define PM1_CNTa			__PM1_CNTa
#define PM1_CNTa_SIZE	__PM1_CNTa_size
#define PM1_CNTb			__PM1_CNTb
#define PM1_CNTb_SIZE	__PM1_CNTb_size

void ACPIInitializeRegisters(void);

#endif //__ASSEMBLY__

#endif //__LOCKDOWN_ACPI_H__
