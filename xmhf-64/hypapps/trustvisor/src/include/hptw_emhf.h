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

#ifndef HPTW_EMHF_H
#define HPTW_EMHF_H

#include <hptw.h>
#include <xmhf.h>
#include <pages.h>

#define HPTW_EMHF_EPT12_INVALID ULLONG_MAX

typedef struct {
  hptw_ctx_t super; /* When nested virtualization, EPT12. Otherwise, EPT01 */
  hptw_ctx_t lower; /* When nested virtualization, EPT01. Otherwise, ignored */
  pagelist_t *pl;
} hptw_emhf_host_ctx_t;
int hptw_emhf_host_ctx_init(hptw_emhf_host_ctx_t *ctx, hpt_pa_t root_pa, hpt_type_t t, pagelist_t *pl);
int hptw_emhf_host_l1_ctx_init_of_vcpu(hptw_emhf_host_ctx_t *rv, VCPU *vcpu);
int hptw_emhf_host_ctx_init_of_vcpu(hptw_emhf_host_ctx_t *rv, VCPU *vcpu);

typedef struct {
  hptw_ctx_t super;

  hptw_cpl_t cpl;

  hptw_emhf_host_ctx_t hptw_host_ctx;
  pagelist_t *pl;
} hptw_emhf_checked_guest_ctx_t;
int hptw_emhf_checked_guest_ctx_init(hptw_emhf_checked_guest_ctx_t *ctx,
                                     hpt_pa_t root_pa,
                                     hpt_type_t t,
                                     hptw_cpl_t cpl,
                                     const hptw_emhf_host_ctx_t *host_ctx,
                                     pagelist_t *pl);
int hptw_emhf_checked_guest_ctx_init_of_vcpu(hptw_emhf_checked_guest_ctx_t *rv, VCPU *vcpu);

// Access EPT12 / NPT12
static inline hpt_pa_t hpt_emhf_get_l1l2_root_pm_pa(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return HPTW_EMHF_EPT12_INVALID;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    HALT_ON_ERRORCOND(0 && "Not implemented");
  } else {
    HALT_ON_ERRORCOND(0);
  }
}

static inline void hpt_emhf_set_l1l2_root_pm_pa(VCPU *vcpu, hpt_pa_t val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    (void)val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    HALT_ON_ERRORCOND(0 && "Not implemented");
  } else {
    HALT_ON_ERRORCOND(0);
  }
}

#endif
