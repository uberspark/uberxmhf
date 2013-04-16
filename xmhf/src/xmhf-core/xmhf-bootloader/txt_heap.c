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

/*
 * heap.c: fns for verifying and printing the Intel(r) TXT heap data structs
 *
 * Copyright (c) 2003-2010, Intel Corporation
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above
 *     copyright notice, this list of conditions and the following
 *     disclaimer in the documentation and/or other materials provided
 *     with the distribution.
 *   * Neither the name of the Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/*
 * Modified for XMHF by jonmccune@cmu.edu, 2011.01.04
 */

#include <xmhf.h> 

static inline void print_heap_hash(sha1_hash_t hash)
{
    print_hash((const tb_hash_t *)hash, TB_HALG_SHA1);
}

static void print_bios_data(bios_data_t *bios_data)
{
    printf("bios_data (@%p, %Lx):\n", bios_data,
           *((uint64_t *)bios_data - 1));
    printf("\t version: %u\n", bios_data->version);
    printf("\t bios_sinit_size: 0x%x (%u)\n", bios_data->bios_sinit_size,
           bios_data->bios_sinit_size);
    printf("\t lcp_pd_base: 0x%Lx\n", bios_data->lcp_pd_base);
    printf("\t lcp_pd_size: 0x%Lx (%Lu)\n", bios_data->lcp_pd_size,
           bios_data->lcp_pd_size);
    printf("\t num_logical_procs: %u\n", bios_data->num_logical_procs);
    if ( bios_data->version >= 3 )
        printf("\t flags: 0x%08Lx\n", bios_data->flags);
}

bool verify_bios_data(txt_heap_t *txt_heap)
{
    uint64_t size, heap_size;
    bios_data_t *bios_data;

    /* check size */
    heap_size = read_priv_config_reg(TXTCR_HEAP_SIZE);
    size = get_bios_data_size(txt_heap);
    if ( size == 0 ) {
        printf("BIOS data size is 0\n");
        return false;
    }
    if ( size > heap_size ) {
        printf("BIOS data size is larger than heap size "
               "(%Lx, heap size=%Lx)\n", size, heap_size);
        return false;
    }

    bios_data = get_bios_data_start(txt_heap);

    /* check version */
    if ( bios_data->version < 2 ) {
        printf("unsupported BIOS data version (%u)\n", bios_data->version);
        return false;
    }
    /* we assume backwards compatibility but print a warning */
    if ( bios_data->version > 3 )
        printf("unsupported BIOS data version (%u)\n", bios_data->version);

    /* all TXT-capable CPUs support at least 2 cores */
    if ( bios_data->num_logical_procs < 2 ) {
        printf("BIOS data has incorrect num_logical_procs (%u)\n",
               bios_data->num_logical_procs);
        return false;
    }
#define NR_CPUS 8 // XXX arbitrary value; use something sane
    else if ( bios_data->num_logical_procs > NR_CPUS ) {
        printf("BIOS data specifies too many CPUs (%u)\n",
               bios_data->num_logical_procs);
        return false;
    }

    print_bios_data(bios_data);

    return true;
}

static void print_os_mle_data(os_mle_data_t *os_mle_data)
{
    printf("os_mle_data (@%p, %Lx):\n", os_mle_data,
           *((uint64_t *)os_mle_data - 1));
    printf("\t version: %u\n", os_mle_data->version);
    /* TBD: perhaps eventually print saved_mtrr_state field */
    printf("\t mbi: %p\n", os_mle_data->mbi);
}

static bool verify_os_mle_data(txt_heap_t *txt_heap)
{
    uint64_t size, heap_size;
    os_mle_data_t *os_mle_data;

    /* check size */
    heap_size = read_priv_config_reg(TXTCR_HEAP_SIZE);
    size = get_os_mle_data_size(txt_heap);
    if ( size == 0 ) {
        printf("OS to MLE data size is 0\n");
        return false;
    }
    if ( size > heap_size ) {
        printf("OS to MLE data size is larger than heap size "
               "(%Lx, heap size=%Lx)\n", size, heap_size);
        return false;
    }
    if ( size != (sizeof(os_mle_data_t) + sizeof(size)) ) {
        printf("OS to MLE data size (%Lx) is not equal to "
               "os_mle_data_t size (%x)\n", size, sizeof(os_mle_data_t));
        return false;
    }

    os_mle_data = get_os_mle_data_start(txt_heap);

    /* check version */
    /* since this data is from our pre-launch to post-launch code only, it */
    /* should always be this */
    if ( os_mle_data->version != 2 ) {
        printf("unsupported OS to MLE data version (%u)\n",
               os_mle_data->version);
        return false;
    }

    /* field checks */
    if ( os_mle_data->mbi == NULL ) {
        printf("OS to MLE data mbi field is NULL\n");
        return false;
    }

    print_os_mle_data(os_mle_data);

    return true;
}

void print_os_sinit_data(os_sinit_data_t *os_sinit_data)
{
    printf("os_sinit_data (@%p, %Lx):\n", os_sinit_data,
           *((uint64_t *)os_sinit_data - 1));
    printf("\t version: %u\n", os_sinit_data->version);
    printf("\t mle_ptab: 0x%Lx\n", os_sinit_data->mle_ptab);
    printf("\t mle_size: 0x%Lx (%Lu)\n", os_sinit_data->mle_size,
           os_sinit_data->mle_size);
    printf("\t mle_hdr_base: 0x%Lx\n", os_sinit_data->mle_hdr_base);
    printf("\t vtd_pmr_lo_base: 0x%Lx\n", os_sinit_data->vtd_pmr_lo_base);
    printf("\t vtd_pmr_lo_size: 0x%Lx\n", os_sinit_data->vtd_pmr_lo_size);
    printf("\t vtd_pmr_hi_base: 0x%Lx\n", os_sinit_data->vtd_pmr_hi_base);
    printf("\t vtd_pmr_hi_size: 0x%Lx\n", os_sinit_data->vtd_pmr_hi_size);
    printf("\t lcp_po_base: 0x%Lx\n", os_sinit_data->lcp_po_base);
    printf("\t lcp_po_size: 0x%Lx (%Lu)\n", os_sinit_data->lcp_po_size,
           os_sinit_data->lcp_po_size);
    print_txt_caps("\t ", os_sinit_data->capabilities);
    if ( os_sinit_data->version >= 5 )
        printf("\t efi_rsdt_ptr: 0x%Lx\n", os_sinit_data->efi_rsdt_ptr);
}

static bool verify_os_sinit_data(txt_heap_t *txt_heap)
{
    uint64_t size, heap_size;
    os_sinit_data_t *os_sinit_data;

    /* check size */
    heap_size = read_priv_config_reg(TXTCR_HEAP_SIZE);
    size = get_os_sinit_data_size(txt_heap);
    if ( size == 0 ) {
        printf("OS to SINIT data size is 0\n");
        return false;
    }
    if ( size > heap_size ) {
        printf("OS to SINIT data size is larger than heap size "
               "(%Lx, heap size=%Lx)\n", size, heap_size);
        return false;
    }

    os_sinit_data = get_os_sinit_data_start(txt_heap);

    /* check version (but since we create this, it should always be OK) */
    if ( os_sinit_data->version < 4 || os_sinit_data->version > 5 ) {
        printf("unsupported OS to SINIT data version (%u)\n",
               os_sinit_data->version);
        return false;
    }

    if ( (os_sinit_data->version == 4 &&
          size != offsetof(os_sinit_data_t, efi_rsdt_ptr) + sizeof(uint64_t))
         || (os_sinit_data->version == 5 &&
             size != sizeof(os_sinit_data_t) + sizeof(uint64_t)) ) {
        printf("OS to SINIT data size (%Lx) does not match for version (%x)\n",
               size, sizeof(os_sinit_data_t));
        return false;
    }

    print_os_sinit_data(os_sinit_data);

    return true;
}

static void print_sinit_mdrs(sinit_mdr_t mdrs[], uint32_t num_mdrs)
{
    static const char *mem_types[] = {"GOOD", "SMRAM OVERLAY",
                                      "SMRAM NON-OVERLAY",
                                      "PCIE EXTENDED CONFIG", "PROTECTED"};
    unsigned int i;

    printf("\t sinit_mdrs:\n");
    for ( i = 0; i < num_mdrs; i++ ) {
        printf("\t\t %016Lx - %016Lx ", mdrs[i].base,
               mdrs[i].base + mdrs[i].length);
        if ( mdrs[i].mem_type < sizeof(mem_types)/sizeof(mem_types[0]) )
            printf("(%s)\n", mem_types[mdrs[i].mem_type]);
        else
            printf("(%d)\n", (int)mdrs[i].mem_type);
    }
}

static void print_sinit_mle_data(sinit_mle_data_t *sinit_mle_data)
{
    printf("sinit_mle_data (@%p, %Lx):\n", sinit_mle_data,
           *((uint64_t *)sinit_mle_data - 1));
    printf("\t version: %u\n", sinit_mle_data->version);
    printf("\t bios_acm_id: \n\t");
    print_heap_hash(sinit_mle_data->bios_acm_id);
    printf("\t edx_senter_flags: 0x%08x\n",
           sinit_mle_data->edx_senter_flags);
    printf("\t mseg_valid: 0x%Lx\n", sinit_mle_data->mseg_valid);
    printf("\t sinit_hash:\n\t"); print_heap_hash(sinit_mle_data->sinit_hash);
    printf("\t mle_hash:\n\t"); print_heap_hash(sinit_mle_data->mle_hash);
    printf("\t stm_hash:\n\t"); print_heap_hash(sinit_mle_data->stm_hash);
    printf("\t lcp_policy_hash:\n\t");
        print_heap_hash(sinit_mle_data->lcp_policy_hash);
    printf("\t lcp_policy_control: 0x%08x\n",
           sinit_mle_data->lcp_policy_control);
    printf("\t rlp_wakeup_addr: 0x%x\n", sinit_mle_data->rlp_wakeup_addr);
    printf("\t num_mdrs: %u\n", sinit_mle_data->num_mdrs);
    printf("\t mdrs_off: 0x%x\n", sinit_mle_data->mdrs_off);
    printf("\t num_vtd_dmars: %u\n", sinit_mle_data->num_vtd_dmars);
    printf("\t vtd_dmars_off: 0x%x\n", sinit_mle_data->vtd_dmars_off);
    print_sinit_mdrs((sinit_mdr_t *)
                     (((void *)sinit_mle_data - sizeof(uint64_t)) +
                      sinit_mle_data->mdrs_off), sinit_mle_data->num_mdrs);
    if ( sinit_mle_data->version >= 8 )
        printf("\t proc_scrtm_status: 0x%08x\n",
               sinit_mle_data->proc_scrtm_status);
}

static bool verify_sinit_mle_data(txt_heap_t *txt_heap)
{
    uint64_t size, heap_size;
    sinit_mle_data_t *sinit_mle_data;

    /* check size */
    heap_size = read_priv_config_reg(TXTCR_HEAP_SIZE);
    size = get_sinit_mle_data_size(txt_heap);
    if ( size == 0 ) {
        printf("SINIT to MLE data size is 0\n");
        return false;
    }
    if ( size > heap_size ) {
        printf("SINIT to MLE data size is larger than heap size\n"
               "(%Lx, heap size=%Lx)\n", size, heap_size);
        return false;
    }

    sinit_mle_data = get_sinit_mle_data_start(txt_heap);

    /* check version */
    sinit_mle_data = get_sinit_mle_data_start(txt_heap);
    if ( sinit_mle_data->version < 6 ) {
        printf("unsupported SINIT to MLE data version (%u)\n",
               sinit_mle_data->version);
        return false;
    }
    else if ( sinit_mle_data->version > 8 ) {
        printf("unsupported SINIT to MLE data version (%u)\n",
               sinit_mle_data->version);
    }

    /* this data is generated by SINIT and so is implicitly trustworthy, */
    /* so we don't need to validate it's fields */

    print_sinit_mle_data(sinit_mle_data);

    return true;
}

bool verify_txt_heap(txt_heap_t *txt_heap, bool bios_data_only)
{
    uint64_t size1, size2, size3, size4;

    /* verify BIOS to OS data */
    if ( !verify_bios_data(txt_heap) )
        return false;

    if ( bios_data_only )
        return true;

    /* check that total size is within the heap */
    size1 = get_bios_data_size(txt_heap);
    size2 = get_os_mle_data_size(txt_heap);
    size3 = get_os_sinit_data_size(txt_heap);
    size4 = get_sinit_mle_data_size(txt_heap);

    /* overflow? */
    if ( plus_overflow_u64(size1, size2) ) {
        printf("TXT heap data size overflows\n");
        return false;
    }
    if ( plus_overflow_u64(size3, size4) ) {
        printf("TXT heap data size overflows\n");
        return false;
    }
    if ( plus_overflow_u64(size1 + size2, size3 + size4) ) {
        printf("TXT heap data size overflows\n");
        return false;
    }

    if ( (size1 + size2 + size3 + size4) >
         read_priv_config_reg(TXTCR_HEAP_SIZE) ) {
        printf("TXT heap data sizes (%Lx, %Lx, %Lx, %Lx) are larger than\n"
               "heap total size (%Lx)\n", size1, size2, size3, size4,
               read_priv_config_reg(TXTCR_HEAP_SIZE));
        return false;
    }

    /* verify OS to MLE data */
    if ( !verify_os_mle_data(txt_heap) )
        return false;

    /* verify OS to SINIT data */
    if ( !verify_os_sinit_data(txt_heap) )
        return false;

    /* verify SINIT to MLE data */
    if ( !verify_sinit_mle_data(txt_heap) )
        return false;

    return true;
}


/*
 * Local variables:
 * mode: C
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
