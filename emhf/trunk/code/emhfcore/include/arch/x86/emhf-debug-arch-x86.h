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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

// EMHF debug component 
// x86 arch. specific declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_DEBUG_ARCH_X86_H__
#define __EMHF_DEBUG_ARCH_X86_H__

#include "_com.h"		//serial UART as debugging backend
#include "_div64.h"		//arch. specific do_div definition

#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------
void emhf_debug_arch_init(char *params);
void emhf_debug_arch_putstr(const char *str);


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------
extern uart_config_t g_uart_config;

//#ifdef __DEBUG_SERIAL__
void dbg_x86_uart_init(char *params);
void dbg_x86_uart_putc(int x);
void dbg_x86_uart_putstr(const char *str);

//#ifdef __DEBUG_VGA__
void dbg_x86_vgamem_init(char *params);
void dbg_x86_vgamem_putc(int c);
void dbg_x86_vgamem_putstr(const char *str);


#endif // __ASSEMBLY__

#endif //__EMHF_DEBUG_ARCH_X86_H__
