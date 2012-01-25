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

#include <emhf.h> 

//open TPM locality
int emhf_tpm_open_locality(int locality){
	int status;

    /* We expect locality 1 or 2 */
    if(locality < 1 || locality > 2) {
        return 1;
    }
	
	status = emhf_tpm_arch_open_locality(locality);

    if(!emhf_tpm_is_tpm_ready(locality)) {
        printf("\n%s: FAILED to open TPM locality %d\n", __FUNCTION__, locality);
        return 1;
    } 

    printf("\n%s: opened TPM locality %d", __FUNCTION__, locality);
    return 0;    
}

//check if TPM is ready for use
bool emhf_tpm_is_tpm_ready(uint32_t locality){
		return emhf_tpm_arch_is_tpm_ready(locality);
}


void cpu_relax(void){
    __asm__ __volatile__ ("pause");
}


/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */



