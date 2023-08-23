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
 * XMHF: The following file is taken from:
 *  tboot-1.10.5/tboot/txt/heap.c
 * Changes made include:
 *  Define NR_CPUS.
 *  Change type of lctx_addr from void * to uint32_t.
 *  TODO: Hardcoding get_evtlog_type() to EVTLOG_TPM2_TCG.
 */

/*
 * heap.c: fns for verifying and printing the Intel(r) TXT heap data structs
 *
 * Copyright (c) 2003-2011, Intel Corporation
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

#include <xmhf.h>

/*
 * extended data elements
 */

/* HEAP_BIOS_SPEC_VER_ELEMENT */
static void print_bios_spec_ver_elt(const heap_ext_data_element_t *elt)
{
    const heap_bios_spec_ver_elt_t *bios_spec_ver_elt =
        (const heap_bios_spec_ver_elt_t *)elt->data;

    printf("\t\t BIOS_SPEC_VER:\n");
    printf("\t\t     major: 0x%x\n", bios_spec_ver_elt->spec_ver_major);
    printf("\t\t     minor: 0x%x\n", bios_spec_ver_elt->spec_ver_minor);
    printf("\t\t     rev: 0x%x\n", bios_spec_ver_elt->spec_ver_rev);
}

/* HEAP_ACM_ELEMENT */
static void print_acm_elt(const heap_ext_data_element_t *elt)
{
    const heap_acm_elt_t *acm_elt = (const heap_acm_elt_t *)elt->data;

    printf("\t\t ACM:\n");
    printf("\t\t     num_acms: %u\n", acm_elt->num_acms);
    for ( unsigned int i = 0; i < acm_elt->num_acms; i++ )
        printf("\t\t     acm_addrs[%u]: 0x%jx\n", i, acm_elt->acm_addrs[i]);
}

/* HEAP_CUSTOM_ELEMENT */
static void print_custom_elt(const heap_ext_data_element_t *elt)
{
    const heap_custom_elt_t *custom_elt = (const heap_custom_elt_t *)elt->data;

    printf("\t\t CUSTOM:\n");
    printf("\t\t     size: %u\n", elt->size);
    printf("\t\t     uuid: "); print_uuid(&custom_elt->uuid);
    printf("\n");
}

/* HEAP_EVENT_LOG_POINTER_ELEMENT */
static inline void print_heap_hash(const sha1_hash_t hash)
{
    print_hash((const tb_hash_t *)hash, TB_HALG_SHA1);
}

void print_event(const tpm12_pcr_event_t *evt)
{
    printf("\t\t\t Event:\n");
    printf("\t\t\t     PCRIndex: %u\n", evt->pcr_index);
    printf("\t\t\t         Type: 0x%x\n", evt->type);
    printf("\t\t\t       Digest: ");
    print_heap_hash(evt->digest);
    printf("\t\t\t         Data: %u bytes", evt->data_size);
    print_hex("\t\t\t         ", evt->data, evt->data_size);
}

static void print_evt_log(const event_log_container_t *elog)
{
    const tpm12_pcr_event_t *curr, *next;

    printf("\t\t\t Event Log Container:\n");
    printf("\t\t\t     Signature: %s\n", elog->signature);
    printf("\t\t\t  ContainerVer: %u.%u\n",
           elog->container_ver_major, elog->container_ver_minor);
    printf("\t\t\t   PCREventVer: %u.%u\n",
           elog->pcr_event_ver_major, elog->pcr_event_ver_minor);
    printf("\t\t\t          Size: %u\n", elog->size);
    printf("\t\t\t  EventsOffset: [%u,%u]\n",
           elog->pcr_events_offset, elog->next_event_offset);

    curr = (tpm12_pcr_event_t *)((void*)elog + elog->pcr_events_offset);
    next = (tpm12_pcr_event_t *)((void*)elog + elog->next_event_offset);

    while ( curr < next ) {
        print_event(curr);
        curr = (void *)curr + sizeof(*curr) + curr->data_size;
    }
}

static void print_evt_log_ptr_elt(const heap_ext_data_element_t *elt)
{
    const heap_event_log_ptr_elt_t *elog_elt =
              (const heap_event_log_ptr_elt_t *)elt->data;

    printf("\t\t EVENT_LOG_POINTER:\n");
    printf("\t\t       size: %u\n", elt->size);
    printf("\t\t  elog_addr: 0x%jx\n", elog_elt->event_log_phys_addr);

    if ( elog_elt->event_log_phys_addr )
        print_evt_log((event_log_container_t *)(unsigned long)
                      elog_elt->event_log_phys_addr);
}

void print_event_2(void *evt, uint16_t alg)
{
    uint32_t hash_size, data_size;
    void *next = evt;

    hash_size = get_hash_size(alg);
    if ( hash_size == 0 )
        return;

    printf("\t\t\t Event:\n");
    printf("\t\t\t     PCRIndex: %u\n", *((uint32_t *)next));

    if ( *((uint32_t *)next) > 24 && *((uint32_t *)next) != 0xFF ) {
         printf("\t\t\t           Wrong Event Log.\n");
         return;
     }

    next += sizeof(uint32_t);
    printf("\t\t\t         Type: 0x%x\n", *((uint32_t *)next));

    if ( *((uint32_t *)next) > 0xFFF ) {
        printf("\t\t\t           Wrong Event Log.\n");
        return;
    }

    next += sizeof(uint32_t);
    printf("\t\t\t       Digest: ");
    print_hex(NULL, (uint8_t *)next, hash_size);
    next += hash_size;
    data_size = *(uint32_t *)next;
    printf("\t\t\t         Data: %u bytes", data_size);
    if ( data_size > 4096 ) {
        printf("\t\t\t           Wrong Event Log.\n");
        return;
    }

    next += sizeof(uint32_t);
    if ( data_size )
         print_hex("\t\t\t         ", (uint8_t *)next, data_size);
    else
         printf("\n");
}

uint32_t print_event_2_1_log_header(void *evt)
{
    tcg_pcr_event *evt_ptr = (tcg_pcr_event *)evt;
    tcg_efi_specid_event_strcut *evt_data_ptr = (tcg_efi_specid_event_strcut *) evt_ptr->event_data;

    printf("\t TCG Event Log Header:\n");
    printf("\t\t       pcr_index: %u\n", evt_ptr->pcr_index);
    printf("\t\t      event_type: %u\n", evt_ptr->event_type);
    printf("\t\t          digest: %s\n", evt_ptr->digest);
    printf("\t\t event_data_size: %u\n", evt_ptr->event_data_size);

    // print out event log header data

    printf("\t\t 	   header event data:  \n");
    printf("\t\t\t              signature: %s\n", evt_data_ptr->signature);
    printf("\t\t\t         platform_class: %u\n", evt_data_ptr->platform_class);
    printf("\t\t\t     spec_version_major: %u\n", evt_data_ptr->spec_version_major);
    printf("\t\t\t     spec_version_minor: %u\n", evt_data_ptr->spec_version_minor);
    printf("\t\t\t            spec_errata: %u\n", evt_data_ptr->spec_errata);
    printf("\t\t\t             uintn_size: %u\n", evt_data_ptr->uintn_size);
    printf("\t\t\t   number_of_algorithms: %u\n", evt_data_ptr->number_of_algorithms);

    for ( uint32_t i = 0; i < evt_data_ptr->number_of_algorithms; i++ ) {
        printf("\t\t\t\t   algorithm_id: 0x%x \n", evt_data_ptr->digestSizes[i].algorithm_id);
        printf("\t\t\t\t    digest_size: %u\n", evt_data_ptr->digestSizes[i].digest_size);
    }

    printf("\t\t\t       vendor_info: %u bytes\n", evt_data_ptr->vendor_info_size);
    print_hex(NULL, evt_data_ptr->vendor_info, evt_data_ptr->vendor_info_size);

    return evt_ptr->event_data_size;
}

uint32_t print_event_2_1(void *evt)
{
    tcg_pcr_event2 *evt_ptr = (tcg_pcr_event2 *)evt;
    uint8_t *evt_data_ptr;
    uint16_t hash_alg;
    uint32_t event_size = 0;
    printf("\t\t\t TCG Event:\n");
    printf("\t\t\t      pcr_index: %u\n", evt_ptr->pcr_index);
    printf("\t\t\t     event_type: 0x%x\n", evt_ptr->event_type);
    printf("\t\t\t          count: %u\n", evt_ptr->digest.count);
    if (evt_ptr->digest.count != 0) {
        evt_data_ptr = (uint8_t *)evt_ptr->digest.digests[0].digest;
        hash_alg = evt_ptr->digest.digests[0].hash_alg;
        for ( uint32_t i = 0; i < evt_ptr->digest.count; i++ ) {
            switch (hash_alg) {
                case TB_HALG_SHA1:
                    printf("SHA1: \n");
                    print_hex(NULL, evt_data_ptr, SHA1_LENGTH);
                    evt_data_ptr += SHA1_LENGTH;
                    break;

                case TB_HALG_SHA256:
                    printf("SHA256: \n");
                    print_hex(NULL, evt_data_ptr, SHA256_LENGTH);
                    evt_data_ptr += SHA256_LENGTH;
                    break;

                case TB_HALG_SM3:
                    printf("SM3_256: \n");
                    print_hex(NULL, evt_data_ptr, SM3_LENGTH);
                    evt_data_ptr += SM3_LENGTH;
                    break;

                case TB_HALG_SHA384:
                    printf("SHA384: \n");
                    print_hex(NULL, evt_data_ptr, SHA384_LENGTH);
                    evt_data_ptr += SHA384_LENGTH;
                    break;

                case TB_HALG_SHA512:
                    printf("SHA512:  \n");
                    print_hex(NULL, evt_data_ptr, SHA512_LENGTH);
                    evt_data_ptr += SHA512_LENGTH;
                    break;
                default:
                    printf("Unsupported algorithm: %u\n", evt_ptr->digest.digests[i].hash_alg);
            }
            hash_alg = (uint16_t)*evt_data_ptr;
            evt_data_ptr += sizeof(uint16_t);
        }
        evt_data_ptr -= sizeof(uint16_t);
        event_size = (uint32_t)*evt_data_ptr;
        printf("\t\t\t     event_data: %u bytes", event_size);
        evt_data_ptr += sizeof(uint32_t);
        print_hex("\t\t\t     ", evt_data_ptr, event_size);
    }
    else {
        printf("sth wrong in TCG event log: algorithm count = %u\n", evt_ptr->digest.count);
        evt_data_ptr= (uint8_t *)evt +12;
    }
    return (evt_data_ptr + event_size - (uint8_t *)evt);
}

static void print_evt_log_ptr_elt_2(const heap_ext_data_element_t *elt)
{
    const heap_event_log_ptr_elt2_t *elog_elt =
              (const heap_event_log_ptr_elt2_t *)elt->data;
    const heap_event_log_descr_t *log_descr;

    printf("\t\t EVENT_LOG_PTR:\n");
    printf("\t\t       size: %u\n", elt->size);
    printf("\t\t      count: %d\n", elog_elt->count);

    for ( unsigned int i=0; i<elog_elt->count; i++ ) {
        uint32_t hash_size, data_size;
        void *curr, *next;

        log_descr = &elog_elt->event_log_descr[i];
        printf("\t\t\t Log Descrption:\n");
        printf("\t\t\t             Alg: %u\n", log_descr->alg);
        printf("\t\t\t            Size: %u\n", log_descr->size);
        printf("\t\t\t    EventsOffset: [%u,%u]\n",
                log_descr->pcr_events_offset,
                log_descr->next_event_offset);

        if (log_descr->pcr_events_offset == log_descr->next_event_offset) {
            printf("\t\t\t              No Event Log.\n");
            continue;
        }

        hash_size = get_hash_size(log_descr->alg);
        if ( hash_size == 0 )
            return;

        curr = (void *)(unsigned long)log_descr->phys_addr +
                log_descr->pcr_events_offset;
        next = (void *)(unsigned long)log_descr->phys_addr +
                log_descr->next_event_offset;

        //It is required for each of the non-SHA1 event log the first entry to be the following
        //TPM1.2 style TCG_PCR_EVENT record specifying type of the log:
        //TCG_PCR_EVENT.PCRIndex = 0
        //TCG_PCR_EVENT.EventType = 0x03 // EV_NO_ACTION per TCG EFI
                                       // Platform specification
        //TCG_PCR_EVENT.Digest = {00…00} // 20 zeros
        //TCG_PCR_EVENT.EventDataSize = sizeof(TCG_LOG_DESCRIPTOR).
        //TCG_PCR_EVENT.EventData = TCG_LOG_DESCRIPTOR
        //The digest of this record MUST NOT be extended into any PCR.

        if (log_descr->alg != TB_HALG_SHA1){
            print_event_2(curr, TB_HALG_SHA1);
            curr += sizeof(tpm12_pcr_event_t) + sizeof(tpm20_log_descr_t);
        }

        while ( curr < next ) {
            print_event_2(curr, log_descr->alg);
            data_size = *(uint32_t *)(curr + 2*sizeof(uint32_t) + hash_size);
            curr += 3*sizeof(uint32_t) + hash_size + data_size;
        }
    }
}

static void print_evt_log_ptr_elt_2_1(const heap_ext_data_element_t *elt)
{
    const heap_event_log_ptr_elt2_1_t *elog_elt = (const heap_event_log_ptr_elt2_1_t *)elt->data;
    void *curr, *next;
    uint32_t event_header_data_size;

    printf("\t TCG EVENT_LOG_PTR:\n");
    printf("\t\t       type: %d\n", elt->type);
    printf("\t\t       size: %u\n", elt->size);
    printf("\t TCG Event Log Descrption:\n");
    printf("\t     allcoated_event_container_size: %u\n", elog_elt->allcoated_event_container_size);
    printf("\t                       EventsOffset: [%u,%u]\n",
           elog_elt->first_record_offset, elog_elt->next_record_offset);

    if (elog_elt->first_record_offset == elog_elt->next_record_offset) {
        printf("\t\t\t No Event Log found.\n");
        return;
    }

    curr = (void *)(unsigned long)elog_elt->phys_addr + elog_elt->first_record_offset;
    next = (void *)(unsigned long)elog_elt->phys_addr + elog_elt->next_record_offset;
    event_header_data_size = print_event_2_1_log_header(curr);

    curr += sizeof(tcg_pcr_event) + event_header_data_size;
    while ( curr < next ) {
        curr += print_event_2_1(curr);
    }
}


static void print_ext_data_elts(const heap_ext_data_element_t elts[])
{
    const heap_ext_data_element_t *elt = elts;

    printf("\t ext_data_elts[]:\n");
    while ( elt->type != HEAP_EXTDATA_TYPE_END ) {
        switch ( elt->type ) {
            case HEAP_EXTDATA_TYPE_BIOS_SPEC_VER:
                print_bios_spec_ver_elt(elt);
                break;
            case HEAP_EXTDATA_TYPE_ACM:
                print_acm_elt(elt);
                break;
            case HEAP_EXTDATA_TYPE_CUSTOM:
                print_custom_elt(elt);
                break;
            case HEAP_EXTDATA_TYPE_TPM_EVENT_LOG_PTR:
                print_evt_log_ptr_elt(elt);
                break;
            case HEAP_EXTDATA_TYPE_TPM_EVENT_LOG_PTR_2:
                print_evt_log_ptr_elt_2(elt);
                break;
            case HEAP_EXTDATA_TYPE_TPM_EVENT_LOG_PTR_2_1:
                print_evt_log_ptr_elt_2_1(elt);
                break;
            default:
                printf("\t\t unknown element:  type: %u, size: %u\n",
                       elt->type, elt->size);
                break;
        }
        elt = (void *)elt + elt->size;
    }
}

static void print_bios_data(const bios_data_t *bios_data, uint64_t size)
{
    printf("bios_data (@%p, %jx):\n", bios_data,
           *((uint64_t *)bios_data - 1));
    printf("\t version: %u\n", bios_data->version);
    printf("\t bios_sinit_size: 0x%x (%u)\n", bios_data->bios_sinit_size,
           bios_data->bios_sinit_size);
    printf("\t lcp_pd_base: 0x%jx\n", bios_data->lcp_pd_base);
    printf("\t lcp_pd_size: 0x%jx (%ju)\n", bios_data->lcp_pd_size,
           bios_data->lcp_pd_size);
    printf("\t num_logical_procs: %u\n", bios_data->num_logical_procs);
    if ( bios_data->version >= 3 )
        printf("\t flags: 0x%08jx\n", bios_data->flags.raw);
    if ( bios_data->version >= 4 && size > sizeof(*bios_data) + sizeof(size) )
        print_ext_data_elts(bios_data->ext_data_elts);
}

static bool verify_bios_spec_ver_elt(const heap_ext_data_element_t *elt)
{
    const heap_bios_spec_ver_elt_t *bios_spec_ver_elt =
        (const heap_bios_spec_ver_elt_t *)elt->data;

    if ( elt->size != sizeof(*elt) + sizeof(*bios_spec_ver_elt) ) {
        printf("HEAP_BIOS_SPEC_VER element has wrong size (%u)\n", elt->size);
        return false;
    }

    /* any values are allowed */
    return true;
}

static bool verify_acm_elt(const heap_ext_data_element_t *elt)
{
    const heap_acm_elt_t *acm_elt = (const heap_acm_elt_t *)elt->data;

    if ( elt->size != sizeof(*elt) + sizeof(*acm_elt) +
         acm_elt->num_acms*sizeof(uint64_t) ) {
        printf("HEAP_ACM element has wrong size (%u)\n", elt->size);
        return false;
    }

    /* no addrs is not error, but print warning */
    if ( acm_elt->num_acms == 0 )
        printf("HEAP_ACM element has no ACM addrs\n");

    for ( unsigned int i = 0; i < acm_elt->num_acms; i++ ) {
        if ( acm_elt->acm_addrs[i] == 0 ) {
            printf("HEAP_ACM element ACM addr (%u) is NULL\n", i);
            return false;
        }

        if ( acm_elt->acm_addrs[i] >= 0x100000000UL ) {
            printf("HEAP_ACM element ACM addr (%u) is >4GB (0x%jx)\n", i,
                   acm_elt->acm_addrs[i]);
            return false;
        }

        /* not going to check if ACM addrs are valid ACMs */
    }

    return true;
}

static bool verify_custom_elt(const heap_ext_data_element_t *elt)
{
    const heap_custom_elt_t *custom_elt = (const heap_custom_elt_t *)elt->data;

    if ( elt->size < sizeof(*elt) + sizeof(*custom_elt) ) {
        printf("HEAP_CUSTOM element has wrong size (%u)\n", elt->size);
        return false;
    }

    /* any values are allowed */
    return true;
}

static bool verify_evt_log(const event_log_container_t *elog)
{
    if ( elog == NULL ) {
        printf("Event log container pointer is NULL\n");
        return false;
    }

    if ( memcmp(elog->signature, EVTLOG_SIGNATURE, sizeof(elog->signature)) ) {
        printf("Bad event log container signature: %s\n", elog->signature);
        return false;
    }

    if ( elog->size != MAX_EVENT_LOG_SIZE ) {
        printf("Bad event log container size: 0x%x\n", elog->size);
        return false;
    }

    /* no need to check versions */

    if ( elog->pcr_events_offset < sizeof(*elog) ||
         elog->next_event_offset < elog->pcr_events_offset ||
         elog->next_event_offset > elog->size ) {
        printf("Bad events offset range: [%u, %u)\n",
               elog->pcr_events_offset, elog->next_event_offset);
        return false;
    }

    return true;
}

static bool verify_evt_log_ptr_elt(const heap_ext_data_element_t *elt)
{
    const heap_event_log_ptr_elt_t *elog_elt =
              (const heap_event_log_ptr_elt_t *)elt->data;

    if ( elt->size != sizeof(*elt) + sizeof(*elog_elt) ) {
        printf("HEAP_EVENT_LOG_POINTER element has wrong size (%u)\n",
               elt->size);
        return false;
    }

    return verify_evt_log((event_log_container_t *)(unsigned long)
                          elog_elt->event_log_phys_addr);
}

static bool verify_evt_log_ptr_elt_2(const heap_ext_data_element_t *elt)
{
    if ( !elt )
        return false;

    return true;
}

static bool verify_ext_data_elts(const heap_ext_data_element_t elts[],
                                 size_t elts_size)
{
    const heap_ext_data_element_t *elt = elts;

    while ( true ) {
        if ( elts_size < sizeof(*elt) ) {
            printf("heap ext data elements too small\n");
            return false;
        }
        if ( elts_size < elt->size || elt->size == 0 ) {
            printf("invalid element size:  type: %u, size: %u\n",
                   elt->type, elt->size);
            return false;
        }
        switch ( elt->type ) {
            case HEAP_EXTDATA_TYPE_END:
                return true;
            case HEAP_EXTDATA_TYPE_BIOS_SPEC_VER:
                if ( !verify_bios_spec_ver_elt(elt) )
                    return false;
                break;
            case HEAP_EXTDATA_TYPE_ACM:
                if ( !verify_acm_elt(elt) )
                    return false;
                break;
            case HEAP_EXTDATA_TYPE_CUSTOM:
                if ( !verify_custom_elt(elt) )
                    return false;
                break;
            case HEAP_EXTDATA_TYPE_TPM_EVENT_LOG_PTR:
                if ( !verify_evt_log_ptr_elt(elt) )
                    return false;
                break;
            case HEAP_EXTDATA_TYPE_TPM_EVENT_LOG_PTR_2:
                if ( !verify_evt_log_ptr_elt_2(elt) )
                    return false;
                break;
            default:
                printf("unknown element:  type: %u, size: %u\n", elt->type,
                       elt->size);
                break;
        }
        elts_size -= elt->size;
        elt = (void *)elt + elt->size;
    }
    return true;
}

bool verify_bios_data(const txt_heap_t *txt_heap)
{
    uint64_t heap_base = read_pub_config_reg(TXTCR_HEAP_BASE);
    uint64_t heap_size = read_pub_config_reg(TXTCR_HEAP_SIZE);
    uint64_t size;
    bios_data_t *bios_data;

    printf("TXT.HEAP.BASE: 0x%jx\n", heap_base);
    printf("TXT.HEAP.SIZE: 0x%jx (%ju)\n", heap_size, heap_size);

    /* verify that heap base/size are valid */
    if ( txt_heap == NULL || heap_base == 0 || heap_size == 0 )
        return false;

    /* check size */
    size = get_bios_data_size(txt_heap);
    if ( size == 0 ) {
        printf("BIOS data size is 0\n");
        return false;
    }
    if ( size > heap_size ) {
        printf("BIOS data size is larger than heap size "
               "(%jx, heap size=%jx)\n", size, heap_size);
        return false;
    }

    bios_data = get_bios_data_start(txt_heap);

    /* check version */
    if ( bios_data->version < 2 ) {
        printf("unsupported BIOS data version (%u)\n", bios_data->version);
        return false;
    }
    /* we assume backwards compatibility but print a warning */
    if ( bios_data->version > 6 )
        printf("unsupported BIOS data version (%u)\n", bios_data->version);

    /* all TXT-capable CPUs support at least 1 core */
    if ( bios_data->num_logical_procs < 1 ) {
        printf("BIOS data has incorrect num_logical_procs (%u)\n",
               bios_data->num_logical_procs);
        return false;
    }
// XMHF: Define NR_CPUS.
#define NR_CPUS (MAX_VCPU_ENTRIES)
    else if ( bios_data->num_logical_procs > NR_CPUS ) {
        printf("BIOS data specifies too many CPUs (%u)\n",
               bios_data->num_logical_procs);
        return false;
    }

    if ( bios_data->version >= 4 && size > sizeof(*bios_data) + sizeof(size) ) {
        if ( !verify_ext_data_elts(bios_data->ext_data_elts,
                                   size - sizeof(*bios_data) - sizeof(size)) )
            return false;
    }

    print_bios_data(bios_data, size);

    return true;
}

static void print_os_mle_data(const os_mle_data_t *os_mle_data)
{
    printf("os_mle_data (@%p, %llx):\n", os_mle_data,
           *((uint64_t *)os_mle_data - 1));
    printf("\t version: %u\n", os_mle_data->version);
    /* TBD: perhaps eventually print saved_mtrr_state field */
    // XMHF: Change type of lctx_addr from void * to uint32_t.
    printf("\t loader context addr: %x\n", os_mle_data->lctx_addr);
}

static bool verify_os_mle_data(const txt_heap_t *txt_heap)
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
               "(%llx, heap size=%llx)\n", size, heap_size);
        return false;
    }
    if ( size != (sizeof(os_mle_data_t) + sizeof(size)) ) {
        printf("OS to MLE data size (%llx) is not equal to "
               "os_mle_data_t size (%x)\n", size, sizeof(os_mle_data_t));
        return false;
    }

    os_mle_data = get_os_mle_data_start(txt_heap);

    /* check version */
    /* since this data is from our pre-launch to post-launch code only, it */
    /* should always be this */
    if ( os_mle_data->version != 3 ) {
        printf("unsupported OS to MLE data version (%u)\n",
               os_mle_data->version);
        return false;
    }

    /* field checks */
    // Change type of lctx_addr from void * to uint32_t.
    if ( (void *)(os_mle_data->lctx_addr) == NULL ) {
        printf("OS to MLE data loader context addr field is NULL\n");
        return false;
    }

    print_os_mle_data(os_mle_data);

    return true;
}

/*
 * Make sure version is in [MIN_OS_SINIT_DATA_VER, MAX_OS_SINIT_DATA_VER]
 * before calling calc_os_sinit_data_size
 */
uint64_t calc_os_sinit_data_size(uint32_t version)
{
    uint64_t size[] = {
        offsetof(os_sinit_data_t, efi_rsdt_ptr) + sizeof(uint64_t),
        sizeof(os_sinit_data_t) + sizeof(uint64_t),
        sizeof(os_sinit_data_t) + sizeof(uint64_t) +
            2 * sizeof(heap_ext_data_element_t) +
            sizeof(heap_event_log_ptr_elt_t)
    };
    struct tpm_if *tpm = get_tpm();
    // TODO: Hardcoding get_evtlog_type() to EVTLOG_TPM2_TCG.
    //int log_type = get_evtlog_type();
    int log_type = EVTLOG_TPM2_TCG;

    if ( log_type == EVTLOG_TPM2_TCG ) {
        size[2] = sizeof(os_sinit_data_t) + sizeof(uint64_t) +
        2 * sizeof(heap_ext_data_element_t) +
        sizeof(heap_event_log_ptr_elt2_1_t);
    } else if (log_type == EVTLOG_TPM2_LEGACY) {
        u32 count;
        if ( tpm->extpol == TB_EXTPOL_AGILE )
            count = tpm->banks;
        else
            if ( tpm->extpol == TB_EXTPOL_EMBEDDED )
                count = tpm->alg_count;
            else
                count = 1;
        size[2] = sizeof(os_sinit_data_t) + sizeof(uint64_t) +
            2 * sizeof(heap_ext_data_element_t) + 4 +
            count*sizeof(heap_event_log_descr_t);
    }

    if ( version >= 6 )
        return size[2];
    else
        return size[version - MIN_OS_SINIT_DATA_VER];
}

void print_os_sinit_data_vtdpmr(const os_sinit_data_t *os_sinit_data)
{
    printf("\t vtd_pmr_lo_base: 0x%llx\n", os_sinit_data->vtd_pmr_lo_base);
    printf("\t vtd_pmr_lo_size: 0x%llx\n", os_sinit_data->vtd_pmr_lo_size);
    printf("\t vtd_pmr_hi_base: 0x%llx\n", os_sinit_data->vtd_pmr_hi_base);
    printf("\t vtd_pmr_hi_size: 0x%llx\n", os_sinit_data->vtd_pmr_hi_size);
}

void print_os_sinit_data(const os_sinit_data_t *os_sinit_data)
{
    printf("os_sinit_data (@%p, %llx):\n", os_sinit_data,
           *((uint64_t *)os_sinit_data - 1));
    printf("\t version: %u\n", os_sinit_data->version);
    printf("\t flags: %u\n", os_sinit_data->flags);
    printf("\t mle_ptab: 0x%llx\n", os_sinit_data->mle_ptab);
    printf("\t mle_size: 0x%llx (%llu)\n", os_sinit_data->mle_size,
           os_sinit_data->mle_size);
    printf("\t mle_hdr_base: 0x%llx\n", os_sinit_data->mle_hdr_base);
    print_os_sinit_data_vtdpmr(os_sinit_data);
    printf("\t lcp_po_base: 0x%llx\n", os_sinit_data->lcp_po_base);
    printf("\t lcp_po_size: 0x%llx (%llu)\n", os_sinit_data->lcp_po_size, os_sinit_data->lcp_po_size);
    print_txt_caps("\t ", os_sinit_data->capabilities);
    if ( os_sinit_data->version >= 5 )
        printf("\t efi_rsdt_ptr: 0x%llx\n", os_sinit_data->efi_rsdt_ptr);
    if ( os_sinit_data->version >= 6 )
        print_ext_data_elts(os_sinit_data->ext_data_elts);
}

static bool verify_os_sinit_data(const txt_heap_t *txt_heap)
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
               "(%llx, heap size=%llx)\n", size, heap_size);
        return false;
    }

    os_sinit_data = get_os_sinit_data_start(txt_heap);

    /* check version (but since we create this, it should always be OK) */
    if ( os_sinit_data->version < MIN_OS_SINIT_DATA_VER ||
         os_sinit_data->version > MAX_OS_SINIT_DATA_VER ) {
        printf("unsupported OS to SINIT data version (%u)\n",
               os_sinit_data->version);
        return false;
    }

    if ( size != calc_os_sinit_data_size(os_sinit_data->version) ) {
        printf("OS to SINIT data size (%llx) does not match for version (%x)\n",
               size, sizeof(os_sinit_data_t));
        return false;
    }

    if ( os_sinit_data->version >= 6 ) {
        if ( !verify_ext_data_elts(os_sinit_data->ext_data_elts,
                                   size - sizeof(*os_sinit_data) - sizeof(size)) )
            return false;
    }

    print_os_sinit_data(os_sinit_data);

    return true;
}

static void print_sinit_mdrs(const sinit_mdr_t mdrs[], uint32_t num_mdrs)
{
    static const char *mem_types[] = {"GOOD", "SMRAM OVERLAY",
                                      "SMRAM NON-OVERLAY",
                                      "PCIE EXTENDED CONFIG", "PROTECTED"};

    printf("\t sinit_mdrs:\n");
    for ( unsigned int i = 0; i < num_mdrs; i++ ) {
        printf("\t\t %016llx - %016llx ", mdrs[i].base,
               mdrs[i].base + mdrs[i].length);
        if ( mdrs[i].mem_type < sizeof(mem_types)/sizeof(mem_types[0]) )
            printf("(%s)\n", mem_types[mdrs[i].mem_type]);
        else
            printf("(%d)\n", (int)mdrs[i].mem_type);
    }
}

static void print_sinit_mle_data(const sinit_mle_data_t *sinit_mle_data)
{
    printf("sinit_mle_data (@%p, %llx):\n", sinit_mle_data,
           *((uint64_t *)sinit_mle_data - 1));
    printf("\t version: %u\n", sinit_mle_data->version);
    printf("\t bios_acm_id: \n\t");
    print_heap_hash(sinit_mle_data->bios_acm_id);
    printf("\t edx_senter_flags: 0x%08x\n",
           sinit_mle_data->edx_senter_flags);
    printf("\t mseg_valid: 0x%llx\n", sinit_mle_data->mseg_valid);
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
    if ( sinit_mle_data->version >= 9 )
        print_ext_data_elts(sinit_mle_data->ext_data_elts);
}

static bool verify_sinit_mle_data(const txt_heap_t *txt_heap)
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
               "(%llx, heap size=%llx)\n", size, heap_size);
        return false;
    }

    sinit_mle_data = get_sinit_mle_data_start(txt_heap);

    /* check version */
    if ( sinit_mle_data->version < 6 ) {
        printf("unsupported SINIT to MLE data version (%u)\n",
               sinit_mle_data->version);
        return false;
    }
    else if ( sinit_mle_data->version > 9 ) {
        printf("unsupported SINIT to MLE data version (%u)\n",
               sinit_mle_data->version);
    }

    /* this data is generated by SINIT and so is implicitly trustworthy, */
    /* so we don't need to validate it's fields */

    print_sinit_mle_data(sinit_mle_data);

    return true;
}

bool verify_txt_heap(const txt_heap_t *txt_heap, bool bios_data_only)
{
    uint64_t size1;
    uint64_t size2;
    uint64_t size3;
    uint64_t size4;

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
        printf("TXT heap data sizes (%llx, %llx, %llx, %llx) are larger than\n"
               "heap total size (%llx)\n", size1, size2, size3, size4,
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
