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

static inline hpt_type_t VCPU_get_hpt_type(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return HPT_TYPE_EPT;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return HPT_TYPE_PAE;
  }

  ASSERT(0);
  return HPT_TYPE_INVALID;
}

static inline hpt_pm_t VCPU_get_default_root_pm(VCPU *vcpu)
{
  return (hpt_pm_t)emhf_memprot_get_default_root_pagemap_address(vcpu);
}

static inline hpt_pm_t VCPU_get_current_root_pm(VCPU *vcpu)
{
  hpt_type_t t = VCPU_get_hpt_type(vcpu);
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return spa2hva(hpt_eptp_get_address(t,
                                        emhf_memprot_get_EPTP(vcpu)));
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return spa2hva(hpt_cr3_get_address(t,
                                       emhf_memprot_get_h_cr3(vcpu)));
  } else {
    ASSERT(0);
    return NULL;
  }
}

static inline void VCPU_set_current_root_pm(VCPU *vcpu, hpt_pm_t root)
{
  hpt_type_t t = VCPU_get_hpt_type(vcpu);
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    emhf_memprot_set_EPTP(vcpu, hpt_eptp_set_address(t,
                                                     emhf_memprot_get_EPTP(vcpu),
                                                     hva2spa(root)));
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    emhf_memprot_set_h_cr3(vcpu, hpt_cr3_set_address(t,
                                                    emhf_memprot_get_h_cr3(vcpu),
                                                    hva2spa(root)));
  } else {
    ASSERT(0);
  }
}

static inline hpt_type_t VCPU_get_guest_hpt_type(VCPU *vcpu) {
  /* XXX assumes NORM or PAE. Need to check for 64-bit */
  return (VCPU_gcr4(vcpu) & CR4_PAE) ? HPT_TYPE_PAE : HPT_TYPE_NORM;
}

static inline hpt_pm_t VCPU_get_current_guest_root_pm(VCPU *vcpu)
{
  return gpa2hva(hpt_cr3_get_address(VCPU_get_guest_hpt_type(vcpu),
                                     VCPU_gcr3(vcpu)));
}

#endif //__ASSEMBLY__


#endif //_HPT_EMHF_H
