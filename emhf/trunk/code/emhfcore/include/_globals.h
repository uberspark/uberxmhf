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

/**
 * globals.h - contains information about global variables used
 * throughout the hypervisor. Trying to keep them all in one place.
 */

#ifndef __GLOBALS_H__
#define __GLOBALS_H__

#ifndef __ASSEMBLY__






//defined in runtimesup.S(.text), this is the start of the real-mode AP
//bootstrap code
extern u32 _ap_bootstrap_start[];

//defined in runtimesup.S(.text), this is the end of the real-mode AP
//bootstrap code
extern u32 _ap_bootstrap_end[];

//defined in runtimesup.S(.text), this is the MLE Join stucture to
//bring up the APs
extern u32 _mle_join_start[];

//the CR3 value to be loaded by the AP boot-strap code is placed in this
//variable by the runtime before waking up the APs
//defined in runtimesup.S(.text)
extern u32 _ap_cr3_value;

//the CR4 value to be loaded by the AP boot-strap code is placed in this
//variable by the runtime before waking up the APs
//defined in runtimesup.S(.text)
extern u32 _ap_cr4_value;


#if defined (__TEST_CPU_QUIESCE__)
	//queisce test global variables
	//quiesce cpu counter and corresponding lock
	extern u32 g_quiesce_cpu_counter __attribute__(( section(".data") ));
	extern u32 g_lock_quiesce_cpu_counter __attribute__(( section(".data") ));
#endif




#endif //__ASSEMBLY__


#endif /* __GLOBALS_H__ */
