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

#include <stdbool.h>

#include <types.h> /* u32, ... */
#include <error.h> /* HALT() */
#include <processor.h> /* rdtsc64() */
#include <target.h>
#include <tpm.h>
#include <tpm_emhf.h> /* hwtpm_open_locality() */
#include <tv_utpm.h>
#include <sha1.h>
#include <random.h> /* rand_bytes_or_die() */
#include <nv.h>

/**
 * Checks that supplied index is defined, is of the appropriate size,
 * and has appropriate access restrictions in place.  Those are PCRs
 * 17 and 18, and accessible for reading and writing exclusively from
 * locality 2.
 *
 * returns 0 on success.
 */
static int validate_mss_nv_region(unsigned int locality,
                                  tpm_nv_index_t idx,
                                  unsigned int expected_size) {
    int rv = 0;
    unsigned int actual_size = 0;

		if(locality == 1000 || idx == 1000) return 1; /* junk */
		
    /* if(0 != (rv = tpm_get_nvindex_size(locality, idx, &actual_size))) { */
    /*     dprintf(LOG_ERROR, "\n[TV] %s: tpm_get_nvindex_size returned an ERROR!", */
    /*             __FUNCTION__); */
    /*     return rv; */
    /* } */

    if(actual_size != expected_size) {
        dprintf(LOG_ERROR, "\n[TV] ERROR: %s: actual_size (%d) != expected_size (%d)!",
                __FUNCTION__, actual_size, expected_size);
        return 1;
    }

    /* XXX TODO XXX: Check ACL on NV Region! */
    dprintf(LOG_ERROR, "\n\n[TV] %s: XXX -- NV REGION ACCESS CONTROL CHECK UNIMPLEMENTED -- XXX\n"
            "Micro-TPM SEALED STORAGE MAY NOT BE SECURE\n\n",
            __FUNCTION__);
    
    return rv;
}


/**
 * Take appropriate action to initialize the Micro-TPM's sealed
 * storage facility by populating the MasterSealingSecret based on the
 * contents of the hardware TPM's NVRAM.
 *
 * jtt nv_definespace --index 0x00015213 --size 20 -o tpm -e ASCII \
 * -p 17,18 -w --permission 0x00000000 --writelocality 2 \
 * --readlocality 2
 *
 * returns 0 on success.
 */

static int _trustvisor_nv_get_mss(unsigned int locality, uint32_t idx,
                                  uint8_t *mss, unsigned int mss_size) {
    int rv;
    unsigned int i;
    unsigned int actual_size = mss_size;
    bool first_boot;

    if(0 != (rv = validate_mss_nv_region(locality, idx, mss_size))) {
        dprintf(LOG_ERROR, "\n\n[TV] %s: ERROR: validate_mss_nv_region FAILED\n",
                __FUNCTION__);
        //return rv;
        dprintf(LOG_ERROR, "\n\n[TV] %s: Don't care; continuing anyways\n",
                __FUNCTION__);
    }

    if(0 != (rv = tpm_nv_read_value(locality, idx, 0, mss, &actual_size))) {
        dprintf(LOG_ERROR, "[TV] %s: tpm_nv_read_value FAILED! with error %d\n",
                __FUNCTION__, rv);
        return rv;
    }

    if(actual_size != mss_size) {
        dprintf(LOG_ERROR, "[TV] %s: NVRAM read size %d != MSS expected size %d\n",
                __FUNCTION__, actual_size, mss_size);
        return 1;
    }

    /**
     * Check whether the read bytes are all 0xff.  If so, we assume
     * "first-boot" and initialize the contents of NV.
     */
    first_boot = true;
    for(i=0; i<actual_size; i++) {
        if(mss[i] != 0xff) {
            first_boot = false;
            break;
        }
    }

    /* TODO: Get random bytes directly from TPM instead of using PRNG
      (for additional simplicitly / less dependence on PRNG
      security) */
    if(first_boot) {
        dprintf(LOG_TRACE, "[TV] %s: first_boot detected!", __FUNCTION__);
        rand_bytes_or_die(mss, mss_size); /* "or_die" is VERY important! */
        if(0 != (rv = tpm_nv_write_value(locality, idx, 0, mss, mss_size))) {
            dprintf(LOG_ERROR, "[TV] %s: ERROR: Unable to write new MSS to TPM NVRAM (%d)!\n",
                    __FUNCTION__, rv);
            return rv;
        }
    }
    
    return rv;
}


static int nv_read(tpm_nv_index_t idx) {
    uint32_t rv;
    uint8_t data[20];
    uint32_t data_size = 20;
    uint32_t locality = 2;

    memset(data, 0xee, data_size); /* something recognizable if read fails */
    
    rv = tpm_nv_read_value(locality, idx, 0, data, &data_size);

    dprintf(LOG_TRACE, "\n[TV] tpm_nv_read_value returned %d.", rv);

    print_hex("data from NV: ", data, data_size);

    return 0; /* TODO: check for failures */
}

int trustvisor_nv_get_mss(unsigned int locality, uint32_t idx,
                          uint8_t *mss, unsigned int mss_size) {
  int rv;

  ASSERT(NULL != mss);
  ASSERT(mss_size >= 20); /* Sanity-check security level wrt SHA-1 */

	dprintf(LOG_TRACE, "\n[TV] %s: locality %d, idx 0x%08x, mss@%p, mss_size %d",
					__FUNCTION__, locality, idx, mss, mss_size);
	
	nv_read(0x00011337); /* hack */
	nv_read(0x00015217); /* hack */
	
  rv = _trustvisor_nv_get_mss(locality, idx, mss, mss_size);
  if(0 == rv) {
      return rv; /* Success. */
  }

  /**
   * Something went wrong in the optimistic attempt to read /
   * initialize the MSS.  If configured conservatively, halt now!
   */
  if(HALT_UPON_NV_PROBLEM) {
    dprintf(LOG_ERROR, "[TV] %s MasterSealingSeed initialization FAILED! SECURITY HALT!\n",
            __FUNCTION__);
    HALT();
  }

  /**
   * If we're still here, then we're configured to attempt to run in a
   * degraded "ephemeral" mode where there is no long-term (across
   * reboots) sealing support.  Complain loudly.  We will still halt
   * if random keys are not available.
   */
  dprintf(LOG_ERROR, "[TV] %s MasterSealingSeed initialization FAILED!\n"
          "Continuing to operate in degraded mode. EMPHEMERAL SEALING ONLY!\n",
          __FUNCTION__);
  rand_bytes_or_die(mss, mss_size);
  
  /* XXX TODO: Eliminate degraded mode once we are sufficiently robust
     to support development and testing without it. */
  return 0;  
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
