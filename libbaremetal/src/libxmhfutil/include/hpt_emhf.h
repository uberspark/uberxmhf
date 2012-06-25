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

/* hpt_emhf.h - HPT abstraction target interface for EMHF
 * author - amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef _HPT_EMHF_H
#define _HPT_EMHF_H

#include <hpt.h>

#ifndef __ASSEMBLY__

static inline hpt_pme_t* hpt_emhf_get_pml1es(VCPU *vcpu){
	return (hpt_pme_t *)emhf_memprot_get_lvl1_pagemap_address(vcpu);

}

static inline hpt_pme_t* hpt_emhf_get_pml2es(VCPU *vcpu){
	return (hpt_pme_t *)emhf_memprot_get_lvl2_pagemap_address(vcpu);
}

static inline hpt_pme_t* hpt_emhf_get_pml3es(VCPU *vcpu){
	return (hpt_pme_t *)emhf_memprot_get_lvl3_pagemap_address(vcpu);
}

static inline hpt_pme_t* hpt_emhf_get_pml4(VCPU *vcpu){
	return (hpt_pme_t *)emhf_memprot_get_lvl4_pagemap_address(vcpu);
}

static inline hpt_type_t hpt_emhf_get_hpt_type(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return HPT_TYPE_EPT;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return HPT_TYPE_PAE;
  }

  ASSERT(0);
  return HPT_TYPE_INVALID;
}

static inline hpt_pm_t hpt_emhf_get_default_root_pm(VCPU *vcpu)
{
  return (hpt_pm_t)emhf_memprot_get_default_root_pagemap_address(vcpu);
}

static inline hpt_pa_t hpt_emhf_get_root_pm_pa(VCPU *vcpu)
{
  hpt_type_t t = hpt_emhf_get_hpt_type(vcpu);
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return hpt_eptp_get_address(t,
                                 emhf_memprot_arch_x86vmx_get_EPTP(vcpu));
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return hpt_cr3_get_address(t,
                               emhf_memprot_arch_x86svm_get_h_cr3(vcpu));
  } else {
    ASSERT(0);
    return 0;
  }
}

static inline void hpt_emhf_set_root_pm_pa(VCPU *vcpu, hpt_pa_t root_pa)
{
  hpt_type_t t = hpt_emhf_get_hpt_type(vcpu);
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    emhf_memprot_arch_x86vmx_set_EPTP( vcpu, hpt_eptp_set_address(t,
                                                                  emhf_memprot_arch_x86vmx_get_EPTP(vcpu),
                                                                  root_pa));
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    emhf_memprot_arch_x86svm_set_h_cr3( vcpu, hpt_cr3_set_address(t,
                                                                  emhf_memprot_arch_x86svm_get_h_cr3(vcpu),
                                                                  root_pa));
  } else {
    ASSERT(0);
  }
}

static inline hpt_pm_t hpt_emhf_get_root_pm(VCPU *vcpu)
{
  return spa2hva( hpt_emhf_get_root_pm_pa( vcpu));
}

static inline void hpt_emhf_set_root_pm(VCPU *vcpu, hpt_pm_t root)
{
  hpt_emhf_set_root_pm_pa( vcpu, hva2spa(root));
}

static inline hpt_type_t hpt_emhf_get_guest_hpt_type(VCPU *vcpu) {
  /* XXX assumes NORM or PAE. Need to check for 64-bit */
  return (VCPU_gcr4(vcpu) & CR4_PAE) ? HPT_TYPE_PAE : HPT_TYPE_NORM;
}

static inline hpt_pa_t hpt_emhf_get_guest_root_pm_pa(VCPU *vcpu)
{
  hpt_type_t t = hpt_emhf_get_guest_hpt_type(vcpu);
  return hpt_cr3_get_address(t,
                             VCPU_gcr3(vcpu));
}

static inline void hpt_emhf_set_guest_root_pm_pa( VCPU *vcpu, hpt_pa_t root_pa)
{
  hpt_type_t t = hpt_emhf_get_guest_hpt_type(vcpu);
  VCPU_gcr3_set(vcpu,
                hpt_cr3_set_address(t,
                                    VCPU_gcr3(vcpu),
                                    root_pa));
}

/* XXX use with extreme caution. guest could have set its cr3 to point
   to a gpa to which it shouldn't have access */
static inline hpt_pm_t hpt_emhf_get_guest_root_pm(VCPU *vcpu)
{
  return gpa2hva( hpt_emhf_get_guest_root_pm_pa( vcpu));
}

static inline void hpt_emhf_set_guest_root_pm( VCPU *vcpu, hpt_pm_t root)
{
  hpt_emhf_set_guest_root_pm_pa( vcpu, hva2gpa( root));
}

static inline void hpt_emhf_get_root_pmo(VCPU *vcpu, hpt_pmo_t *root)
{
  hpt_type_t t = hpt_emhf_get_hpt_type(vcpu);
  *root = (hpt_pmo_t) {
    .pm = hpt_emhf_get_root_pm(vcpu),
    .t = t,
    .lvl = hpt_root_lvl(t),
  };
}

static inline void hpt_emhf_get_guest_root_pmo(VCPU *vcpu, hpt_pmo_t *root)
{
  hpt_type_t t = hpt_emhf_get_guest_hpt_type(vcpu);
  *root = (hpt_pmo_t) {
    .pm = hpt_emhf_get_guest_root_pm(vcpu),
    .t = t,
    .lvl = hpt_root_lvl(t),
  };
}


#endif //__ASSEMBLY__


#endif //_HPT_EMHF_H
