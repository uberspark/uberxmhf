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

/* hpt_emhf.h - HPT abstraction target interface for EMHF
 * author - amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef _HPT_EMHF_H
#define _HPT_EMHF_H

#include <hpt.h>

#ifndef __ASSEMBLY__

static inline hpt_pme_t* VCPU_get_pml1es(VCPU *vcpu){
	return (hpt_pme_t *)emhf_memprot_get_lvl1_pagemap_address(vcpu);

}

static inline hpt_pme_t* VCPU_get_pml2es(VCPU *vcpu){
	return (hpt_pme_t *)emhf_memprot_get_lvl2_pagemap_address(vcpu);

}

static inline hpt_pme_t* VCPU_get_pml3es(VCPU *vcpu){
	return (hpt_pme_t *)emhf_memprot_get_lvl3_pagemap_address(vcpu);
	
	
}

static inline hpt_pme_t* VCPU_get_pml4(VCPU *vcpu){
	return (hpt_pme_t *)emhf_memprot_get_lvl4_pagemap_address(vcpu);
}


#endif //__ASSEMBLY__


#endif //_HPT_EMHF_H
