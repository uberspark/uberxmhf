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

// nested-x86vmx-vmcs12-fields.h
// Enumerate through all VMCS fields
// author: Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef DECLARE_FIELD_16_RO
 #ifdef DECLARE_FIELD_16
  #define DECLARE_FIELD_16_RO(encoding, name, extra) \
          DECLARE_FIELD_16(encoding, name, extra)
 #else
  #define DECLARE_FIELD_16_RO(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_32_RO
 #ifdef DECLARE_FIELD_32
  #define DECLARE_FIELD_32_RO(encoding, name, extra) \
          DECLARE_FIELD_32(encoding, name, extra)
 #else
  #define DECLARE_FIELD_32_RO(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_64_RO
 #ifdef DECLARE_FIELD_64
  #define DECLARE_FIELD_64_RO(encoding, name, extra) \
          DECLARE_FIELD_64(encoding, name, extra)
 #else
  #define DECLARE_FIELD_64_RO(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_NW_RO
 #ifdef DECLARE_FIELD_NW
  #define DECLARE_FIELD_NW_RO(encoding, name, extra) \
          DECLARE_FIELD_NW(encoding, name, extra)
 #else
  #define DECLARE_FIELD_NW_RO(encoding, name, extra)
 #endif
#endif
#ifndef DECLARE_FIELD_16_RW
 #ifdef DECLARE_FIELD_16
  #define DECLARE_FIELD_16_RW(encoding, name, extra) \
          DECLARE_FIELD_16(encoding, name, extra)
 #else
  #define DECLARE_FIELD_16_RW(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_32_RW
 #ifdef DECLARE_FIELD_32
  #define DECLARE_FIELD_32_RW(encoding, name, extra) \
          DECLARE_FIELD_32(encoding, name, extra)
 #else
  #define DECLARE_FIELD_32_RW(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_64_RW
 #ifdef DECLARE_FIELD_64
  #define DECLARE_FIELD_64_RW(encoding, name, extra) \
          DECLARE_FIELD_64(encoding, name, extra)
 #else
  #define DECLARE_FIELD_64_RW(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_NW_RW
 #ifdef DECLARE_FIELD_NW
  #define DECLARE_FIELD_NW_RW(encoding, name, extra) \
          DECLARE_FIELD_NW(encoding, name, extra)
 #else
  #define DECLARE_FIELD_NW_RW(encoding, name, extra)
 #endif
#endif

DECLARE_FIELD_32_RO(0x4400, info_vminstr_error, UNDEFINED)
DECLARE_FIELD_64_RO(0x2400, guest_paddr, UNDEFINED)
DECLARE_FIELD_NW_RO(0x6400, info_exit_qualification, UNDEFINED)
DECLARE_FIELD_16_RW(0x0000, control_vpid, UNDEFINED)
DECLARE_FIELD_32_RW(0x4000, control_VMX_pin_based, UNDEFINED)
DECLARE_FIELD_64_RW(0x2000, control_IO_BitmapA_address, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6000, control_CR0_mask, UNDEFINED)

#undef DECLARE_FIELD_16_RO
#undef DECLARE_FIELD_32_RO
#undef DECLARE_FIELD_64_RO
#undef DECLARE_FIELD_NW_RO
#undef DECLARE_FIELD_16_RW
#undef DECLARE_FIELD_32_RW
#undef DECLARE_FIELD_64_RW
#undef DECLARE_FIELD_NW_RW

#ifdef DECLARE_FIELD_16
#undef DECLARE_FIELD_16
#endif

#ifdef DECLARE_FIELD_32
#undef DECLARE_FIELD_32
#endif

#ifdef DECLARE_FIELD_64
#undef DECLARE_FIELD_64
#endif

#ifdef DECLARE_FIELD_NW
#undef DECLARE_FIELD_NW
#endif

