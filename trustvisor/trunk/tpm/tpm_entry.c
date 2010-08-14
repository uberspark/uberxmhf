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
 * slbcore.c - entry point from assembly for doing the application's
 * work in a Flicker session.  Also contains code to reconstruct page
 * tables for resumption of Linux kernel.
 *
 * Copyright (C) 2006-2008 Jonathan M. McCune
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2.0 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#include <types.h>
#include <error.h>
#include <multiboot.h>
#include <string.h>
#include <print.h>
#include <svm.h>
#include <sha1.h>
#include <processor.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <io.h>
#include <pci.h>
#include <dev.h>
#include <tpm.h>

#define ktpm_name "ktpm"

int tpm_prepare_tpm(void)
{
    int tpm;

    if(0 >= (tpm = slb_tis_init())) {
        slb_out_description("tis init failed", tpm);
        return -60;
    }

    //slb_out_description("TIS_LOCALITY_3 value is", TIS_LOCALITY_3);

    //slb_debug_locality(TIS_LOCALITY_3);

    if(!slb_tis_access(TIS_LOCALITY_3, 0)) {
        slb_out_info("could not gain TIS ownership at LOCALITY 3");
        //slb_debug_locality(TIS_LOCALITY_3);
    
        if(!slb_tis_access(TIS_LOCALITY_3, 1)) {
            slb_out_info("could not force TIS ownership at LOCALITY 3");
            //slb_debug_locality(TIS_LOCALITY_3);
            return -61;
        } else {
            slb_out_info("TIS ownership forced at LOCALITY 3");
            //slb_debug_locality(TIS_LOCALITY_3);     
        }
    } else {
        slb_out_info("TIS ownership at LOCALITY 3");
        //slb_debug_locality(TIS_LOCALITY_3); 
    }    

    return tpm;
}

int tpm_dowork(void) {
    unsigned int i;
    int ret;
    unsigned char buffer[TCG_BUFFER_SIZE];
    unsigned char buffer2[TCG_BUFFER_SIZE];
    unsigned char pcr[20]; /* for verifying seal is working correctly */
    
    if((ret = tpm_prepare_tpm()) < 1) {
        slb_out_description("ERROR: slb_prepare_tpm returned:", ret);
        ret = -1; /* TODO: set an output parameter */
        goto tpm_error;
    }

    /* Print PCR values */
    for(i=17;i<19;i++) {    
        if((ret = slb_TPM_PcrRead(buffer, i, pcr))) {
            slb_out_description("ERROR in slb_TPM_PcrRead", ret);
        }
        printf("PCR-%02d: ", i);
        dump_bytes(pcr, 20);
    }
    memset(buffer2, 0x00, 20);

#if 0
    /* Do a test TPM_Extend */
    if((ret = slb_TPM_Extend(buffer, 10 /* 17 */, buffer2))) {
        slb_out_description("TPM extend failed", ret);
    }
    slb_out_info("TPM_Extend done\n");
    
    /* Do a test TPM_GetRandom */
    if((ret = TPM_GetRandom(buffer, 20, buffer2))) {
        printf("TPM_GetRandom failed %d\n", ret);
    }
    printf("20 bytes from TPM_GetRandom: ");
    dump_bytes(buffer2, 20);
#endif

#if 0    
    /* Deactivate all localities so that the legacy OS can regain
     * access at the desired locality. */
    if(slb_tis_deactivate_all()) {
        slb_out_info("tis_deactivate failed");
        ret = -62;
        goto tpm_error;
    }
#endif
  tpm_error:
    return 0;    
}

void tpm_deactive(void)
{
  int ret;
  /* Deactivate all localities so that the legacy OS can regain                                                                                     
   * access at the desired locality. */
  if(slb_tis_deactivate_all()) {
    slb_out_info("tis_deactivate failed");
    ret = -62;
    goto tpm_error;
  }
tpm_error:
  return;
}
void init_tpm(void)
{
  tpm_dowork();
}
