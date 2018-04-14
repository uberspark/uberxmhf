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

#ifndef _NV_H_
#define _NV_H_

/* Currently this file depends on tpm.h having been included earlier
 * (for tpm_nv_index_t).  Given that there are also such dependencies
 * for uint32_t, VCPU, etc., I choose to do nothing in here. */

/* TODO: Make the index a boot-time parameter with a sane default */
#define HW_TPM_MASTER_SEALING_SECRET_INDEX 0x00015213
#define HW_TPM_MASTER_SEALING_SECRET_SIZE 20
/* TODO: Make this a build-time config option */
#define HALT_UPON_NV_PROBLEM 0

/* Use Locality 2 for hardware TPM operations involving NV RAM */
#define TRUSTVISOR_HWTPM_NV_LOCALITY 2

#define HW_TPM_ROLLBACK_PROT_INDEX 0x00014E56 /* "NV" */
#define HW_TPM_ROLLBACK_PROT_SIZE 32 /* SHA-256 */

int validate_trustvisor_nv_region(unsigned int locality,
                                  tpm_nv_index_t idx,
                                  unsigned int expected_size);

int trustvisor_nv_get_mss(unsigned int locality, uint32_t idx,
                          uint8_t *mss, unsigned int mss_size);

uint32_t hc_tpmnvram_getsize(VCPU* vcpu, uint32_t size_addr);
uint32_t hc_tpmnvram_readall(VCPU* vcpu, uint32_t out_addr);
uint32_t hc_tpmnvram_writeall(VCPU* vcpu, uint32_t in_addr);

#endif /* _NV_H_ */
