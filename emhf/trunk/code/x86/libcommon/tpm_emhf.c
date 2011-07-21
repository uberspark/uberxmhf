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
 * Author: Jonathan McCune
 */

#include <target.h>
#include <txt.h>
#include <tpm.h> /* generic (tboot-inspired) TPM functions */
#include <tpm_emhf.h> /* EMHF-specific TPM functions */

/* Open TPM Locality 'locality'.  Cope with AMD and Intel CPUs, pre-
 * and post-DRTM, and (TODO) play nice with an OS driver that already
 * has the TPM open at a lesser Locality.
 *
 * Returns 0 on success.
 */
int hwtpm_open_locality(int locality) {
    /* We expect locality 1 or 2 */
    if(locality < 1 || locality > 2) {
        return 1;
    }

    if(get_cpu_vendor_or_die() == CPU_VENDOR_INTEL) {
        txt_didvid_t didvid;
        txt_ver_fsbif_emif_t ver;

        /* display chipset fuse and device and vendor id info */
        didvid._raw = read_pub_config_reg(TXTCR_DIDVID);
        printf("\nHWTPM: chipset ids: vendor: 0x%x, device: 0x%x, revision: 0x%x\n",
               didvid.vendor_id, didvid.device_id, didvid.revision_id);
        ver._raw = read_pub_config_reg(TXTCR_VER_FSBIF);
        if ( (ver._raw & 0xffffffff) == 0xffffffff ||
             (ver._raw & 0xffffffff) == 0x00 )         /* need to use VER.EMIF */
            ver._raw = read_pub_config_reg(TXTCR_VER_EMIF);
        printf("\nHWTPM: chipset production fused: %x\n", ver.prod_fused );
        
        if(txt_is_launched()) {
            write_priv_config_reg(locality == 1 ? TXTCR_CMD_OPEN_LOCALITY1
                                  : TXTCR_CMD_OPEN_LOCALITY2, 0x01);
            read_priv_config_reg(TXTCR_E2STS);   /* just a fence, so ignore return */
        } else {
            printf("\nHWTPM: ERROR: Locality opening UNIMPLEMENTED on Intel without SENTER\n");
            return 1;
        }        
    } else { /* AMD */        
        /* some systems leave locality 0 open for legacy software */
        //dump_locality_access_regs();
        deactivate_all_localities();
        //dump_locality_access_regs();
        
        if(TPM_SUCCESS == tpm_wait_cmd_ready(locality)) {
            printf("\nHWTPM: TPM successfully opened in Locality %d.\n", locality);            
        } else {
            printf("\nHWTPM: TPM ERROR: Locality %d could not be opened.\n", locality);
            return 1;
        }
    }
    
    if(!is_tpm_ready(locality)) {
        printf("\nHWTPM: FAILED to open TPM locality %d\n", locality);
        return 1;
    } 

    printf("\nHWTPM: Opened TPM locality %d\n", locality);
    return 0;    
}




/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */



