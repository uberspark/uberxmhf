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

#include <nv.h>

/* TODO: Make this configurable on the command line with a sane default. */
#define TRUSTVISOR_NV_INDEX 0x00011337

static int nv_read(void) {
    uint32_t rv;
    tpm_nv_index_t idx = TRUSTVISOR_NV_INDEX;
    uint8_t data[64];
    uint32_t data_size = 64;
    uint32_t locality = 2;

    memset(data, 0xee, data_size); /* something recognizable if read fails */
    
    rv = tpm_nv_read_value(locality, idx, 0, data, &data_size);

    dprintf(LOG_TRACE, "\n[TV] tpm_nv_read_value returned %d.", rv);

    print_hex("data from NV: ", data, data_size);

    return 0; /* TODO: check for failures */
}

static int nv_write(void) {
    uint32_t rv=0, i;
    tpm_nv_index_t idx = TRUSTVISOR_NV_INDEX;
    uint8_t data[64];
    uint32_t data_size = 64;
    uint32_t locality = 2;

    for(i=0; i<data_size; i++) data[i] = i; /* something recognizable */
    
    rv = tpm_nv_write_value(locality, idx, 0, data, data_size);

    dprintf(LOG_TRACE, "\n[TV] tpm_nv_write_value returned %d.", rv);

    return 0; /* TODO: check for failures */
}


int trustvisor_nv_init(void) {
  uint32_t rv = 0;
  dprintf(LOG_TRACE, "\n[TV] trustvisor_nv_init started.");

  /* Do an initial read */
  rv = nv_read();

  /* then try to write the value */
  rv = nv_write();

  /* then try to read the new value */
  rv = nv_read();
  
  return rv;
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
