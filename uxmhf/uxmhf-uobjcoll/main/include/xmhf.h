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

// xmhf.h - main XMHF header file
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_H_
#define __XMHF_H_

#include <uberspark/include/uberspark.h>
#include <uberspark/uobjrtl/hw/include/generic/x86_32/intel/hw.h>
#include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>
// #include <uberspark/uobjrtl/debug/include/debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-config.h>          //XMHF platform/arch config, TODO: this needs to be platform/arch independent push arch dependent stuff into arch/
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-types.h>           //XMHF specific base types
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-error.h>			//error handling
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc.h>					//core framework decls.

#define _XDPRINTF_(format, args...)
#define MACRO_EXPANSION_WORKAROUND(func, ...) func(__VA_ARGS__) // used to expand macros before they get stringized (https://gcc.gnu.org/onlinedocs/cpp/Argument-Prescan.html)

#endif /* __XMHF_H_ */
