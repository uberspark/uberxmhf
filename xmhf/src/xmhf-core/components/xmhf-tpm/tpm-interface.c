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
 * Common EMHF-specific functions for initiating and terminating
 * communication with the TPM.  Motivation is that AMD and Intel have
 * slightly different requirements, since Intel uses some TXT-specific
 * registers if late launch has already completed.
 *
 * TODO: For dynamic hypervisor launch after the legacy OS is booted,
 * support to "play nice" with the legacy OS's TPM driver probably
 * goes in here.
 *
 * Author: Jonathan McCune and Amit Vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h> 

//open TPM locality
int emhf_tpm_open_locality(int locality){
    /* We expect locality 1 or 2 */
    if(locality < 1 || locality > 2) {
        return 1;
    }
	
    if(emhf_tpm_arch_open_locality(locality)) {
      printf("\n%s: FAILED to open TPM locality %d\n", __FUNCTION__, locality);
      return 1;
    };

    if(!emhf_tpm_is_tpm_ready(locality)) {
        printf("\n%s: ERROR TPM is not ready, failed to open locality %d\n", __FUNCTION__, locality);
        return 1;
    } 

    printf("\n%s: opened TPM locality %d", __FUNCTION__, locality);
    return 0;    
}

//check if TPM is ready for use
bool emhf_tpm_is_tpm_ready(uint32_t locality){
		return emhf_tpm_arch_is_tpm_ready(locality);
}

//deactivate all TPM localities
void emhf_tpm_deactivate_all_localities(void){
	emhf_tpm_arch_deactivate_all_localities();
}

//prepare TPM for use
bool emhf_tpm_prepare_tpm(void){
	return emhf_tpm_arch_prepare_tpm();
}




/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
