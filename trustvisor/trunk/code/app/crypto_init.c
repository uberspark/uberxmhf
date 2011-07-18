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
 * Initialize critical TrustVisor cryptography.
 *
 * Author: Jonathan McCune
 */

#include <stdbool.h>

#include <types.h> /* u32, ... */
#include <processor.h> /* rdtsc64() */
#include <target.h>
#include <tpm.h>

#include <nist_ctr_drbg.h>

#include <crypto_init.h>

/* awesome trick from http://www.jaggersoft.com/pubs/CVu11_3.html */
#define COMPILE_TIME_ASSERT(pred) \
    switch(0){case 0:case pred:;}

static NIST_CTR_DRBG g_drbg; /* SECURITY: this is very sensitive! */
static bool g_master_crypto_init_completed = false;

/* Don't want to get optimized out. */
void zeroize(uint8_t* _p, unsigned int len) {    
    volatile uint8_t *p = _p;
    unsigned int i;
    
    for(i=0; i<len; i++) {
        ((volatile uint8_t *)p)[i] = 0;
		}
}

/* returns 0 on success. */
int get_hw_tpm_entropy(uint8_t* buf, unsigned int len) {
    if(!buf) { return 1; }

    
}

/* returns 0 on success. */
/* TODO: take ciphertext input, e.g., from a multiboot_t */
int trustvisor_master_crypto_init(void) {
    uint8_t EntropyInput[CTR_DRBG_SEED_BITS/8];
    uint64_t Nonce;


    
    nist_ctr_initialize();

    /* Get CTR_DRBG_SEED_BITS of entropy from the hardware TPM */

    /* Use rdtsc to get CTR_DRBG_NONCE_BITS of initialization nonce */
    COMPILE_TIME_ASSERT(CTR_DRBG_NONCE_BITS/8 == sizeof(Nonce));
    Nonce = rdtsc64();

	nist_ctr_drbg_instantiate(&g_drbg, EntropyInput, sizeof(EntropyInput),
                              &Nonce, sizeof(Nonce), NULL, 0);

    
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
