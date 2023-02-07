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

// nested-x86vmx-vmcs12-guesthost.h
// Enumerate through VMCS guest state and host state field pairs
// author: Eric Li (xiaoyili@andrew.cmu.edu)

/*
 * Macros are defined as DECLARE_FIELDPAIR_<size>
 * size is 16, 64, 32, or NW (natural width).
 * The arguments are:
 * * guest_encoding: field encoding used in VMRAED and VMWRITE for guest
 * * host_encoding: field encoding used in VMRAED and VMWRITE for host
 * * name: guest_<name> and host_<name> are the name of the field in struct
 *         nested_vmcs12
 */

#ifndef DECLARE_FIELDPAIR_16
#define DECLARE_FIELDPAIR_16(...)
#endif

#ifndef DECLARE_FIELDPAIR_64
#define DECLARE_FIELDPAIR_64(...)
#endif

#ifndef DECLARE_FIELDPAIR_32
#define DECLARE_FIELDPAIR_32(...)
#endif

#ifndef DECLARE_FIELDPAIR_NW
#define DECLARE_FIELDPAIR_NW(...)
#endif

DECLARE_FIELDPAIR_16(0x0800, 0x0C00, ES_selector)
DECLARE_FIELDPAIR_16(0x0802, 0x0C02, CS_selector)
DECLARE_FIELDPAIR_16(0x0804, 0x0C04, SS_selector)
DECLARE_FIELDPAIR_16(0x0806, 0x0C06, DS_selector)
DECLARE_FIELDPAIR_16(0x0808, 0x0C08, FS_selector)
DECLARE_FIELDPAIR_16(0x080A, 0x0C0A, GS_selector)
DECLARE_FIELDPAIR_16(0x080E, 0x0C0C, TR_selector)
DECLARE_FIELDPAIR_32(0x482A, 0x4C00, SYSENTER_CS)
DECLARE_FIELDPAIR_NW(0x6800, 0x6C00, CR0)
DECLARE_FIELDPAIR_NW(0x6802, 0x6C02, CR3)
DECLARE_FIELDPAIR_NW(0x6804, 0x6C04, CR4)
DECLARE_FIELDPAIR_NW(0x680E, 0x6C06, FS_base)
DECLARE_FIELDPAIR_NW(0x6810, 0x6C08, GS_base)
DECLARE_FIELDPAIR_NW(0x6814, 0x6C0A, TR_base)
DECLARE_FIELDPAIR_NW(0x6816, 0x6C0C, GDTR_base)
DECLARE_FIELDPAIR_NW(0x6818, 0x6C0E, IDTR_base)
DECLARE_FIELDPAIR_NW(0x6824, 0x6C10, SYSENTER_ESP)
DECLARE_FIELDPAIR_NW(0x6826, 0x6C12, SYSENTER_EIP)
DECLARE_FIELDPAIR_NW(0x681C, 0x6C14, RSP)
DECLARE_FIELDPAIR_NW(0x681E, 0x6C16, RIP)

#undef DECLARE_FIELDPAIR_16
#undef DECLARE_FIELDPAIR_64
#undef DECLARE_FIELDPAIR_32
#undef DECLARE_FIELDPAIR_NW
