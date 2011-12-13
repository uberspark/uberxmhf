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

// EMHF memory protection component 
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_MEMPROT_H__
#define __EMHF_MEMPROT_H__


#ifndef __ASSEMBLY__

//initialize memory protection for a core
void emhf_memprot_initialize(VCPU *vcpu);
void emhf_memprot_arch_vmx_initialize(VCPU *vcpu);	//intel VMX arch. backend
void emhf_memprot_arch_svm_initialize(VCPU *vcpu);	//amd SVM arch. backend

// get level-1 page map address
u64 * emhf_memprot_get_lvl1_pagemap_address(VCPU *vcpu);

//get level-2 page map address
u64 * emhf_memprot_get_lvl2_pagemap_address(VCPU *vcpu);

//get level-3 page map address
u64 * emhf_memprot_get_lvl3_pagemap_address(VCPU *vcpu);

//get level-4 page map address
u64 * emhf_memprot_get_lvl4_pagemap_address(VCPU *vcpu);

//get default root page map address
void * emhf_memprot_get_default_root_pagemap_address(VCPU *vcpu);

//get current root page map address
spa_t emhf_memprot_get_current_root_pagemap_address(VCPU *vcpu);

//set current root page map address
void emhf_memprot_set_current_root_pagemap_address(VCPU *vcpu, spa_t root);

	

#endif	//__ASSEMBLY__

#endif //__EMHF_MEMPROT_H__
