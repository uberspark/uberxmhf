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

/*
 * \brief   TIS access routines
 * \date    2006-03-28
 * \author  Bernhard Kauer <kauer@tudos.org>
 */
/*
 * Copyright (C) 2006  Bernhard Kauer <kauer@tudos.org>
 * Technische Universitaet Dresden, Operating Systems Research Group
 *
 * This file is part of the OSLO package, which is distributed under
 * the  terms  of the  GNU General Public Licence 2.  Please see the
 * COPYING file for details.
 */
/**
 * Modified by Jonathan M. McCune for use with Flicker in 2007.
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
#include <delay.h>
#include <tis.h>

/**
 * TIS base address.
 */
#define TIS_BASE_PHYS 0xfed40000

/**
 * Address of the TIS locality.
 */
static unsigned int tis_base = (unsigned int)-1;

/**
 * Init the TIS driver.
 * Returns a TIS_INIT_* value.
 */
enum tis_init
slb_tis_init(void)
{
    struct tis_id *id;
    int i;

    slb_out_description("entered slb_tis_init phys base", TIS_BASE_PHYS);
#if 0
    tis_base = (u32)ioremap_nocache(TIS_BASE_PHYS, 0x5000);
#else
    tis_base = TIS_BASE_PHYS;
#endif
    slb_out_description("entered slb_tis_init virt base", tis_base);

    id = (struct tis_id *)(tis_base + TPM_DID_VID_0);
    i = id->did_vid;
    slb_out_description("id->did_vid: ", i);
    
    switch (id->did_vid)
    {
        case 0x2e4d5453:   /* "STM." */
            slb_out_description("TPM STM rev:", id->rid);
            return TIS_INIT_STM;
        case 0xb15d1:
            slb_out_description("TPM Infinion rev:", id->rid);
            return TIS_INIT_INFINEON;
        case 0x100214e4: /* Broadcom */
            slb_out_description("TPM Broadcom rev", id->rid);
            return TIS_INIT_BROADCOM;
	case 0x4a100000:
            slb_out_description("TPM on Dell T105 rev", id->rid);
            return TIS_INIT_OTHERS;
	case 0x32031114:
            slb_out_description("TPM on Dell Optiplex 740 rev", id->rid);
            return TIS_INIT_OTHERS;
        case 0:
        case -1:
            slb_out_info("No TPM found!");
            return TIS_INIT_NO_TPM;
        default:
            slb_out_description("Unknown TPM found! ID:", id->did_vid);
            return TIS_INIT_NO_TPM;
    }
}


/**
 * Deactivate all localities.
 */
int
slb_tis_deactivate_all(void)
{
    int res = 0;
    unsigned i;
    for (i=0; i<4; i++)
    {
        volatile struct tis_mmap *mmap = (struct tis_mmap *)(tis_base+(i<<12));
        mmap->access = TIS_ACCESS_ACTIVE;
        res |= mmap->access & TIS_ACCESS_ACTIVE;
    }
    return res;
}


/**
 * Request access for a given locality.
 * @param locality: address of the locality e.g. TIS_LOCALITY_2
 * Returns 0 if we could not gain access.
 */
int
slb_tis_access(int locality, int force)
{
/*     int ret; */
    volatile struct tis_mmap *mmap;
    slb_assert(locality>=TIS_LOCALITY_0 && locality <= TIS_LOCALITY_4);

    
    mmap = (struct tis_mmap *)(tis_base + locality);

    if(!(mmap->access & TIS_ACCESS_VALID)) {
        slb_out_info("access register not valid");
        return 0;
    }
    if(mmap->access & TIS_ACCESS_ACTIVE) {
        slb_out_description("locality already active:", locality);
        return 1;
    }

    mmap->access = force ? TIS_ACCESS_TO_SEIZE : TIS_ACCESS_REQUEST;

    slb_wait(10);
    // make the tpm ready -> abort a command
    mmap->sts_base = TIS_STS_CMD_READY;

    return mmap->access & TIS_ACCESS_ACTIVE;
}


void
slb_wait_state(volatile struct tis_mmap *mmap, unsigned state)
{
    unsigned i;
/*     char *str; */
    
    for (i=0; i<750; i++) {
        if((mmap->sts_base & state)==state) {
/*             LIT(str, "slb_wait_state got done early:"); */
/*             slb_out_description(str, i); */
            return;
        }
        slb_wait(1);
    }
}


/**
 * Write the given buffer to the TPM.
 * Returns the numbers of bytes transfered or an value < 0 on errors.
 */
int
slb_tis_write(const unsigned char *buffer, unsigned int size,
              int locality)
{
    volatile struct tis_mmap *mmap;
    int res;

    slb_assert(locality>=TIS_LOCALITY_0 && locality <= TIS_LOCALITY_4);
    mmap = (struct tis_mmap *) (tis_base + locality);
    
    if (!(mmap->sts_base & TIS_STS_CMD_READY))
    {
        // make the tpm ready -> wakeup from idle state
        mmap->sts_base = TIS_STS_CMD_READY;
        slb_wait_state(mmap, TIS_STS_CMD_READY);
        mmap->sts_base = TIS_STS_CMD_READY;                
    }
    CHECK3(-1, !(mmap->sts_base & TIS_STS_CMD_READY), "tis_write() not ready");


    for(res=0; (unsigned int)res < size;res++)
        mmap->data_fifo = *buffer++;

    slb_wait_state(mmap, TIS_STS_VALID);
/*     LIT(str, "TPM sts_base:"); */
/*     slb_out_description(str, (unsigned int)(mmap->sts_base & 0xff)); */

    if(mmap->sts_base & TIS_STS_EXPECT) {
        slb_out_description("TPM expects more data:", (unsigned int)(mmap->sts_base & 0xff));
        return -2;
    } 

    //execute the command
    mmap->sts_base = TIS_STS_TPM_GO;    

    return res;
}


/**
 * Read into the given buffer from the TPM.
 * Returns the numbers of bytes received or an value < 0 on errors.
 */
int
slb_tis_read(unsigned char *buffer, unsigned int size, int locality)
{
    volatile struct tis_mmap *mmap;
    int res = 0;

    slb_assert(locality>=TIS_LOCALITY_0 && locality <= TIS_LOCALITY_4);
    mmap = (struct tis_mmap *) (tis_base + locality);
 
    slb_wait_state(mmap, TIS_STS_VALID | TIS_STS_DATA_AVAIL);
    if(!(mmap->sts_base & TIS_STS_VALID)) {
        slb_out_description("slb_tis_read: sts not valid:", mmap->sts_base);
        return -2;
    }

    for (res=0; (unsigned int)res < size && mmap->sts_base & TIS_STS_DATA_AVAIL; res++)
        *buffer++ = mmap->data_fifo;

    if(mmap->sts_base & TIS_STS_DATA_AVAIL) {
        slb_out_description("more data available: ", mmap->sts_base);
        return -3;
    }

    /* if we're reading 0 bytes, don't make the tpm 'ready' again */
    if(!res) { return res; } 
    
    // make the tpm ready again -> this allows tpm background jobs to complete
    mmap->sts_base = TIS_STS_CMD_READY;
    return res;
}


/**
 * Transmit a command to the TPM and wait for the response.
 * This is our high level TIS function used by all TPM commands.
 */
int
slb_tis_transmit(unsigned char *buffer, unsigned int write_count,
                 unsigned int read_count, int locality)
{
    int res;

    slb_assert(locality>=TIS_LOCALITY_0 && locality <= TIS_LOCALITY_4);
   
    //slb_out_description("TIS write_count", write_count); 
    res = slb_tis_write(buffer, write_count, locality);
    if(res <= 0) {
        slb_out_description("TIS write error: ", res);
        return -1;
    }
    //slb_out_description("TIS transmit 1st: write : ", res);
  
    res = slb_tis_read(buffer, read_count, locality);
    if(res <= 0) {
        slb_out_description("TIS read error: ", res);
        return -2;
    }
    //slb_out_description("TIS transmit 2nd: read : ", res);

    return res;
}
