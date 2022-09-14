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

// dbg-event-logger.c
// All types of events in event logger for debugging
// Author(s): Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef DEFINE_EVENT_FIELD
#error "DEFINE_EVENT_FIELD must be defined"
#endif

/*
 * Arguments of macro DEFINE_EVENT_FIELD:
 * name: Name of the event
 * count_type: type of the cache value (count)
 * count_fmt: format string to print the count
 * lru_size: size of the LRU cache
 * index_type: type of the cache index
 * key_type: type of the cache key
 * key_fmt: format string to print the key
 */

DEFINE_EVENT_FIELD(vmexit_cpuid, u32, "%d", 4, u16, u32, "0x%08x")
DEFINE_EVENT_FIELD(vmexit_rdmsr, u32, "%d", 4, u16, u32, "0x%08x")
DEFINE_EVENT_FIELD(vmexit_wrmsr, u32, "%d", 4, u16, u32, "0x%08x")
DEFINE_EVENT_FIELD(vmexit_xcph, u32, "%d", 4, u16, u8, "0x%02x")
DEFINE_EVENT_FIELD(vmexit_other, u32, "%d", 8, u16, u32, "%d")

#ifdef __NESTED_VIRTUALIZATION__
DEFINE_EVENT_FIELD(vmexit_201, u32, "%d", 8, u16, u32, "%d")
DEFINE_EVENT_FIELD(vmexit_202, u32, "%d", 4, u16, u32, "%d")
DEFINE_EVENT_FIELD(ept02_full, u32, "%d", 2, u16, gpa_t, "0x%08llx")
#endif /* !__NESTED_VIRTUALIZATION__ */

#undef DEFINE_EVENT_FIELD

