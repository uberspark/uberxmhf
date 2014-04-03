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

/**
 * smpg-x86vmx-data.c
 * EMHF SMP guest component x86 (VMX) backend data
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
#include <xmhf.h> 

//the BSP LAPIC base address
//smpguest x86vmx
u32 g_vmx_lapic_base __attribute__(( section(".data") )) = 0;

//4k buffer which is the virtual LAPIC page that guest reads and writes from/to
//during INIT-SIPI-SIPI emulation
//smpguest x86vmx
u8 g_vmx_virtual_LAPIC_base[PAGE_SIZE_4K] __attribute__(( section(".palign_data") ));

//the quiesce counter, all CPUs except for the one requesting the
//quiesce will increment this when they get their quiesce signal
//smpguest x86vmx
u32 g_vmx_quiesce_counter __attribute__(( section(".data") )) = 0;

//SMP lock to access the above variable
//smpguest x86vmx
u32 g_vmx_lock_quiesce_counter __attribute__(( section(".data") )) = 1; 

//resume counter to rally all CPUs after resumption from quiesce
//smpguest x86vmx
u32 g_vmx_quiesce_resume_counter __attribute__(( section(".data") )) = 0;

//SMP lock to access the above variable
//smpguest x86vmx
u32 g_vmx_lock_quiesce_resume_counter __attribute__(( section(".data") )) = 1; 
    
//the "quiesce" variable, if 1, then we have a quiesce in process
//smpguest x86vmx
u32 g_vmx_quiesce __attribute__(( section(".data") )) = 0;;      

//SMP lock to access the above variable
//smpguest x86vmx
u32 g_vmx_lock_quiesce __attribute__(( section(".data") )) = 1; 
    
//resume signal, becomes 1 to signal resume after quiescing
//smpguest x86vmx
u32 g_vmx_quiesce_resume_signal __attribute__(( section(".data") )) = 0;  

//SMP lock to access the above variable
//smpguest x86vmx
u32 g_vmx_lock_quiesce_resume_signal __attribute__(( section(".data") )) = 1; 
