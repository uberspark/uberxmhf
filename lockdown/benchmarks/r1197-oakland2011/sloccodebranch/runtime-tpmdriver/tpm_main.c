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


#include <lockdown/types.h>
#include <lockdown/print.h>
#include <lockdown/lockdown.h>
#include <lockdown/msr.h>
#include <lockdown/processor.h>
#include <lockdown/svm.h>
#include <lockdown/paging.h>
#include <lockdown/io.h>
#include <lockdown/pci.h>

#include <tpm/tpm.h>

#define ktpm_name "ktpm"

int slb_prepare_tpm(void)
{
    int tpm;

    if(0 >= (tpm = slb_tis_init())) {
        slb_out_description("tis init failed", tpm);
        return -60;
    }

    printk("TIS_LOCALITY_3 values is 0x%x\n", TIS_LOCALITY_3);

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

void
slb_run_tests(void) {
    slb_out_info("in slb_run_tests()");
}


int slb_dowork(void) {
    int ret;
    unsigned char buffer[TCG_BUFFER_SIZE];
    unsigned char buffer2[TCG_BUFFER_SIZE];
    unsigned char pcr17[20]; /* for verifying seal is working correctly */
    
    slb_out_info("entered slb_dowork()");

    if((ret = slb_prepare_tpm()) < 1) {
        slb_out_description("ERROR: slb_prepare_tpm returned:", ret);
        ret = -1; /* TODO: set an output parameter */
        goto tpm_error;
    }

    /* dump value of PCR 17; necessary to confirm results thanks to
     * buggy-bug */
    if((ret = slb_TPM_PcrRead(buffer, 17, pcr17))) {
        memset(pcr17, 0x66, 20); /* observable in SSHD */
        slb_out_description("ERROR in slb_TPM_PcrRead", ret);
    }
    slb_dump_bytes(buffer, TCG_BUFFER_SIZE);
    slb_dump_bytes(pcr17, 20);
    printk("PcrRead done\n");

    memset(buffer2, 0x00, 20);
    /* Extend("bottom") */
    if((ret = slb_TPM_Extend(buffer, 10 /* 17 */, buffer2))) {
        slb_out_description("TPM extend failed", ret);
        memset(pcr17, 0x17, 20);
    }
    printk("TPM_Extend done\n");
    
    /* Deactivate all localities so that the legacy OS can regain
     * access at the desired locality. */
    if(slb_tis_deactivate_all()) {
        slb_out_info("tis_deactivate failed");
        ret = -62;
        goto tpm_error;
    }

  tpm_error:
    return 0;    
}
