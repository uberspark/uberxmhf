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
 GEEC sentinel low-level support routines
 author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_sentinel.h>


////// exceptions entry stubs

#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	CASM_FUNCDEF(void, __xmhf_exception_handler_##vector, 					\
    { \
        xmhfhwm_cpu_insn_pushl_imm(vector); \
        xmhfhwm_cpu_insn_pushal(); \
        xmhfhwm_cpu_insn_movw_imm_ax(__DS_CPL0); \
        xmhfhwm_cpu_insn_movw_ax_ds();\
        xmhfhwm_cpu_insn_movw_ax_es();\
        xmhfhwm_cpu_insn_pushl_esp(); \
        xmhfhwm_cpu_insn_call(_geec_sentinel_exception_stub); \
        xmhfhwm_cpu_insn_hlt(); \
    },\
    void *noparam) \

#define XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(vector) 												\
	CASM_FUNCDEF(void, __xmhf_exception_handler_##vector, 					\
    {\
		xmhfhwm_cpu_insn_pushl_imm(0x0); \
        xmhfhwm_cpu_insn_pushl_imm(vector); \
        xmhfhwm_cpu_insn_pushal(); \
        xmhfhwm_cpu_insn_movw_imm_ax(__DS_CPL0); \
        xmhfhwm_cpu_insn_movw_ax_ds();\
        xmhfhwm_cpu_insn_movw_ax_es();\
        xmhfhwm_cpu_insn_pushl_esp(); \
        xmhfhwm_cpu_insn_call(_geec_sentinel_exception_stub); \
        xmhfhwm_cpu_insn_hlt(); \
    },\
    void *noparam) \



XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(0)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(1)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(2)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(3)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(4)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(5)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(6)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(7)
XMHF_EXCEPTION_HANDLER_DEFINE(8)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(9)
XMHF_EXCEPTION_HANDLER_DEFINE(10)
XMHF_EXCEPTION_HANDLER_DEFINE(11)
XMHF_EXCEPTION_HANDLER_DEFINE(12)
XMHF_EXCEPTION_HANDLER_DEFINE(13)
XMHF_EXCEPTION_HANDLER_DEFINE(14)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(15)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(16)
XMHF_EXCEPTION_HANDLER_DEFINE(17)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(18)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(19)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(20)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(21)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(22)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(23)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(24)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(25)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(26)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(27)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(28)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(29)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(30)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(31)





