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

// EMHF base platform component 
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_BASEPLATFORM_H__
#define __EMHF_BASEPLATFORM_H__


#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//exported DATA 


//----------------------------------------------------------------------
//exported FUNCTIONS 

//get CPU vendor
u32 emhf_baseplatform_getcpuvendor(void);

//initialize CPU state
void emhf_baseplatform_cpuinitialize(void);

//initialize SMP
void emhf_baseplatform_smpinitialize(void);

//initialize basic platform elements
void emhf_baseplatform_initialize(void);



//----------------------------------------------------------------------
//arch. backends
u32 emhf_arch_baseplatform_getcpuvendor(void);

u8 emhf_arch_baseplatform_flat_readu8(u32 addr);
u32 emhf_arch_baseplatform_flat_readu32(u32 addr);
void emhf_arch_baseplatform_flat_writeu32(u32 addr, u32 val);
void emhf_arch_baseplatform_flat_writeu64(u32 addr, u64 val);
u64 emhf_arch_baseplatform_flat_readu64(u32 addr);
void emhf_arch_baseplatform_flat_copy(u8 *dest, u8 *src, u32 size);


void emhf_arch_x86_baseplatform_wakeupAPs(void);
void emhf_arch_x86vmx_baseplatform_cpuinitialize(void);

#endif	//__ASSEMBLY__

#endif //__EMHF_BASEPLATFORM_H__
