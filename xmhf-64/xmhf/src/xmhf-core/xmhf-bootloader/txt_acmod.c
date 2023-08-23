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
 *  tboot-1.10.5/tboot/txt/acmod.c
 * Changes made include:
 *  Change return type of __getsec_capabilities() to uint32_t.
 *  Remove RACM functions.
 *  TODO: Commented verify_IA32_se_svn_status().
 *  Remove check of params.acm_max_size in verify_acmod().
 */

/*
 * acmod.c: support functions for use of Intel(r) TXT Authenticated
 *          Code (AC) Modules
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

static acm_info_table_t *get_acmod_info_table(const acm_hdr_t* hdr)
{
    uint32_t user_area_off;

    /* overflow? */
    if ( plus_overflow_u32(hdr->header_len, hdr->scratch_size) ) {
        printf("ACM header length plus scratch size overflows\n");
        return NULL;
    }

    if ( multiply_overflow_u32((hdr->header_len + hdr->scratch_size), 4) ) {
        printf("ACM header length and scratch size in bytes overflows\n");
        return NULL;
    }


    /* this fn assumes that the ACM has already passed at least the initial */
    /* is_acmod() checks */

    user_area_off = (hdr->header_len + hdr->scratch_size) * 4;

    /* overflow? */
    if ( plus_overflow_u32(user_area_off, sizeof(acm_info_table_t)) ) {
        printf("user_area_off plus acm_info_table_t size overflows\n");
        return NULL;
    }

    /* check that table is within module */
    if ( user_area_off + sizeof(acm_info_table_t) > hdr->size*4 ) {
        printf("ACM info table size too large: %x\n",
               user_area_off + (uint32_t)sizeof(acm_info_table_t));
        return NULL;
    }

    /* overflow? */
    if ( plus_overflow_u32((uint32_t)(uintptr_t)hdr, user_area_off) ) {
        printf("hdr plus user_area_off overflows\n");
        return NULL;
    }

    return (acm_info_table_t *)((unsigned long)hdr + user_area_off);
}

static acm_chipset_id_list_t *get_acmod_chipset_list(const acm_hdr_t* hdr)
{
    acm_info_table_t* info_table;
    uint32_t size, id_list_off;
    acm_chipset_id_list_t *chipset_id_list;

    /* this fn assumes that the ACM has already passed the is_acmod() checks */

    info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL )
        return NULL;
    id_list_off = info_table->chipset_id_list;

    size = hdr->size * 4;

    /* overflow? */
    if ( plus_overflow_u32(id_list_off, sizeof(acm_chipset_id_list_t)) ) {
        printf("id_list_off plus acm_chipset_id_list_t size overflows\n");
        return NULL;
    }

    /* check that chipset id table is w/in ACM */
    if ( id_list_off + sizeof(acm_chipset_id_list_t) > size ) {
        printf("ACM chipset id list is too big: chipset_id_list=%x\n",
               id_list_off);
        return NULL;
    }

    /* overflow? */
    if ( plus_overflow_u32((uint32_t)(uintptr_t)hdr, id_list_off) ) {
        printf("hdr plus id_list_off overflows\n");
        return NULL;
    }

    chipset_id_list = (acm_chipset_id_list_t *)
                             ((unsigned long)hdr + id_list_off);

    /* overflow? */
    if ( multiply_overflow_u32(chipset_id_list->count,
             sizeof(acm_chipset_id_t)) ) {
        printf("size of acm_chipset_id_list overflows\n");
        return NULL;
    }
    if ( plus_overflow_u32(id_list_off + sizeof(acm_chipset_id_list_t),
        chipset_id_list->count * sizeof(acm_chipset_id_t)) ) {
        printf("size of all entries overflows\n");
        return NULL;
    }

    /* check that all entries are w/in ACM */
    if ( id_list_off + sizeof(acm_chipset_id_list_t) +
         chipset_id_list->count * sizeof(acm_chipset_id_t) > size ) {
        printf("ACM chipset id entries are too big:"
               " chipset_id_list->count=%x\n", chipset_id_list->count);
        return NULL;
    }

    return chipset_id_list;
}

static acm_processor_id_list_t *get_acmod_processor_list(const acm_hdr_t* hdr)
{
    acm_info_table_t* info_table;
    uint32_t size, id_list_off;
    acm_processor_id_list_t *proc_id_list;

    /* this fn assumes that the ACM has already passed the is_acmod() checks */

    info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL )
        return NULL;
    id_list_off = info_table->processor_id_list;

    size = hdr->size * 4;

    /* overflow? */
    if ( plus_overflow_u32(id_list_off, sizeof(acm_processor_id_list_t)) ) {
        printf("id_list_off plus acm_processor_id_list_t size overflows\n");
        return NULL;
    }

    /* check that processor id table is w/in ACM */
    if ( id_list_off + sizeof(acm_processor_id_list_t) > size ) {
        printf("ACM processor id list is too big: processor_id_list=%x\n",
               id_list_off);
        return NULL;
    }

    /* overflow? */
    if ( plus_overflow_u32((unsigned long)hdr, id_list_off) ) {
        printf("hdr plus id_list_off overflows\n");
        return NULL;
    }

    proc_id_list = (acm_processor_id_list_t *)
                             ((unsigned long)hdr + id_list_off);

    /* overflow? */
    if ( multiply_overflow_u32(proc_id_list->count,
             sizeof(acm_processor_id_t)) ) {
        printf("size of acm_processor_id_list overflows\n");
        return NULL;
    }
    if ( plus_overflow_u32(id_list_off + sizeof(acm_processor_id_list_t),
        proc_id_list->count * sizeof(acm_processor_id_t)) ) {
        printf("size of all entries overflows\n");
        return NULL;
    }

    /* check that all entries are w/in ACM */
    if ( id_list_off + sizeof(acm_processor_id_list_t) +
         proc_id_list->count * sizeof(acm_processor_id_t) > size ) {
        printf("ACM processor id entries are too big:"
               " proc_id_list->count=%x\n", proc_id_list->count);
        return NULL;
    }

    return proc_id_list;
}

tpm_info_list_t *get_tpm_info_list(const acm_hdr_t* hdr)
{
    acm_info_table_t* info_table;
    uint32_t size, tpm_info_off;
    tpm_info_list_t *tpm_info;

    /* this fn assumes that the ACM has already passed the is_acmod() checks */

    info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL )
        return NULL;
    tpm_info_off = info_table->tpm_info_list_off;

    size = hdr->size * 4;

    /* overflow? */
    if ( plus_overflow_u32(tpm_info_off, sizeof(tpm_info_list_t)) ) {
        printf("tpm_info_off plus tpm_info_list_t size overflows\n");
        return NULL;
    }

    /* check that tpm info list is w/in ACM */
    if ( tpm_info_off + sizeof(tpm_info_list_t) > size ) {
        printf("TPM info list is too big: tpm_info_list=%x\n",
               tpm_info_off);
        return NULL;
    }

    /* overflow? */
    if ( plus_overflow_u32((unsigned long)hdr, tpm_info_off) ) {
        printf("hdr plus tpm_info_off overflows\n");
        return NULL;
    }

    tpm_info = (tpm_info_list_t *)
                             ((unsigned long)hdr + tpm_info_off);

    /* overflow? */
    if ( multiply_overflow_u32(tpm_info->count,
             sizeof(uint16_t)) ) {
        printf("size of tpm_info_list overflows\n");
        return NULL;
    }
    if ( plus_overflow_u32(tpm_info_off + sizeof(tpm_info_list_t),
        tpm_info->count * sizeof(uint16_t)) ) {
        printf("size of all entries overflows\n");
        return NULL;
    }

    /* check that all entries are w/in ACM */
    if ( tpm_info_off + sizeof(tpm_info_list_t) +
         tpm_info->count * sizeof(uint16_t) > size ) {
        printf("TPM info list entries are too big:"
               " tpm_info_list->count=%x\n", tpm_info->count);
        return NULL;
    }

    return tpm_info;
}

void print_txt_caps(const char *prefix, txt_caps_t caps)
{
    printf("%scapabilities: 0x%08x\n", prefix, caps._raw);
    printf("%s    rlp_wake_getsec: %d\n", prefix, caps.rlp_wake_getsec);
    printf("%s    rlp_wake_monitor: %d\n", prefix, caps.rlp_wake_monitor);
    printf("%s    ecx_pgtbl: %d\n", prefix, caps.ecx_pgtbl);
    printf("%s    stm: %d\n", prefix, caps.stm);
    printf("%s    pcr_map_no_legacy: %d\n", prefix, caps.pcr_map_no_legacy);
    printf("%s    pcr_map_da: %d\n", prefix, caps.pcr_map_da);
    printf("%s    platform_type: %d\n", prefix, caps.platform_type);
    printf("%s    max_phy_addr: %d\n", prefix, caps.max_phy_addr);
    printf("%s    tcg_event_log_format: %d\n", prefix, caps.tcg_event_log_format);
    printf("%s    cbnt_supported: %d\n", prefix, caps.cbnt_supported);
}

static void print_acm_hdr(const acm_hdr_t *hdr, const char *mod_name)
{
    acm_info_table_t *info_table;
    acm_chipset_id_list_t *chipset_id_list;

    printf("AC module header dump for %s:\n",
           (mod_name == NULL) ? "?" : mod_name);

    /* header */
    printf("\t type: 0x%x ", hdr->module_type);
    if ( hdr->module_type == ACM_TYPE_CHIPSET )
        printf("(ACM_TYPE_CHIPSET)\n");
    else
        printf("(unknown)\n");
    printf("\t subtype: 0x%x ", hdr->module_subtype);
    if ( hdr->module_subtype == ACM_SUBTYPE_RESET )
        printf("(execute at reset)\n");
    else if ( hdr->module_subtype == 0 )
        printf("\n");
    else
        printf("(unknown)\n");
    printf("\t length: 0x%x (%u)\n", hdr->header_len, hdr->header_len);
    printf("\t version: %u\n", hdr->header_ver);
    printf("\t chipset_id: 0x%x\n", (uint32_t)hdr->chipset_id);
    printf("\t flags: 0x%x\n", (uint32_t)hdr->flags._raw);
    printf("\t\t pre_production: %d\n", (int)hdr->flags.pre_production);
    printf("\t\t debug_signed: %d\n", (int)hdr->flags.debug_signed);
    printf("\t vendor: 0x%x\n", hdr->module_vendor);
    printf("\t date: 0x%08x\n", hdr->date);
    printf("\t size*4: 0x%x (%u)\n", hdr->size*4, hdr->size*4);
    printf("\t txt_svn: 0x%08x\n", hdr->txt_svn);
    printf("\t se_svn: 0x%08x\n", hdr->se_svn);
    printf("\t code_control: 0x%x\n", hdr->code_control);
    printf("\t entry point: 0x%08x:%08x\n", hdr->seg_sel,
           hdr->entry_point);
    printf("\t scratch_size: 0x%x (%u)\n", hdr->scratch_size,
           hdr->scratch_size);

    /* info table */
    printf("\t info_table:\n");
    info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL ) {
        printf("\t\t <invalid>\n");
        return;
    }
    printf("\t\t uuid: "); print_uuid(&info_table->uuid);
    printf("\n");
    if ( are_uuids_equal(&(info_table->uuid), &((uuid_t)ACM_UUID_V3)) )
        printf("\t\t     ACM_UUID_V3\n");
    else
        printf("\t\t     unknown\n");
    printf("\t\t chipset_acm_type: 0x%x ",
           (uint32_t)info_table->chipset_acm_type);
    if ( info_table->chipset_acm_type == ACM_CHIPSET_TYPE_SINIT )
        printf("(SINIT)\n");
    else if ( info_table->chipset_acm_type == ACM_CHIPSET_TYPE_BIOS )
        printf("(BIOS)\n");
    else
        printf("(unknown)\n");
    printf("\t\t version: %u\n", (uint32_t)info_table->version);
    printf("\t\t length: 0x%x (%u)\n", (uint32_t)info_table->length,
           (uint32_t)info_table->length);
    printf("\t\t chipset_id_list: 0x%x\n", info_table->chipset_id_list);
    printf("\t\t os_sinit_data_ver: 0x%x\n", info_table->os_sinit_data_ver);
    printf("\t\t min_mle_hdr_ver: 0x%08x\n", info_table->min_mle_hdr_ver);
    print_txt_caps("\t\t ", info_table->capabilities);
    printf("\t\t acm_ver: %u\n", (uint32_t)info_table->acm_ver);
    if (info_table->version > 6) {
        printf("\t\t acm_revision: %x.%x.%x\n",
               (uint32_t)info_table->acm_revision[0],
               (uint32_t)info_table->acm_revision[1],
               (uint32_t)info_table->acm_revision[2]);
    }

    /* chipset list */
    printf("\t chipset list:\n");
    chipset_id_list = get_acmod_chipset_list(hdr);
    if ( chipset_id_list == NULL ) {
        printf("\t\t <invalid>\n");
        return;
    }
    printf("\t\t count: %u\n", chipset_id_list->count);
    for ( unsigned int i = 0; i < chipset_id_list->count; i++ ) {
        acm_chipset_id_t *chipset_id;
        printf("\t\t entry %u:\n", i);
        chipset_id = &(chipset_id_list->chipset_ids[i]);
        printf("\t\t     flags: 0x%x\n", chipset_id->flags);
        printf("\t\t     vendor_id: 0x%x\n", (uint32_t)chipset_id->vendor_id);
        printf("\t\t     device_id: 0x%x\n", (uint32_t)chipset_id->device_id);
        printf("\t\t     revision_id: 0x%x\n",
               (uint32_t)chipset_id->revision_id);
        printf("\t\t     extended_id: 0x%x\n", chipset_id->extended_id);
    }

    if ( info_table->version >= 4 ) {
        acm_processor_id_list_t *proc_id_list;
        /* processor list */
        printf("\t processor list:\n");
        proc_id_list = get_acmod_processor_list(hdr);
        if ( proc_id_list == NULL ) {
            printf("\t\t <invalid>\n");
            return;
        }
        printf("\t\t count: %u\n", proc_id_list->count);
        for ( unsigned int i = 0; i < proc_id_list->count; i++ ) {
            acm_processor_id_t *proc_id;
            printf("\t\t entry %u:\n", i);
            proc_id = &(proc_id_list->processor_ids[i]);
            printf("\t\t     fms: 0x%x\n", proc_id->fms);
            printf("\t\t     fms_mask: 0x%x\n", proc_id->fms_mask);
            printf("\t\t     platform_id: 0x%llx\n", (unsigned long long)proc_id->platform_id);
            printf("\t\t     platform_mask: 0x%llx\n", (unsigned long long)proc_id->platform_mask);
        }
    }

    if ( info_table->version >= 5 ){
        tpm_info_list_t *info_list;
        /* tpm infor list */
        printf("\t TPM info list:\n");
        info_list = get_tpm_info_list(hdr);
        if ( info_list == NULL ) {
            printf("\t\t <invalid>\n");
            return;
        }
        printf("\t\t TPM capability:\n");
        printf("\t\t      ext_policy: 0x%x\n", info_list->capabilities.ext_policy);
        printf("\t\t      tpm_family : 0x%x\n", info_list->capabilities.tpm_family);
        printf("\t\t      tpm_nv_index_set : 0x%x\n", info_list->capabilities.tpm_nv_index_set);
        printf("\t\t alg count: %u\n", info_list->count);
        for ( unsigned int i = 0; i < info_list->count; i++ ) {
            printf("\t\t     alg_id: 0x%x\n", info_list->alg_id[i]);
        }
    }
}

uint32_t get_supported_os_sinit_data_ver(const acm_hdr_t* hdr)
{
    /* assumes that it passed is_sinit_acmod() */

    acm_info_table_t *info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL )
        return 0;

    return info_table->os_sinit_data_ver;
}

// XMHF: Change return type of __getsec_capabilities() to uint32_t.
uint32_t get_sinit_capabilities(const acm_hdr_t* hdr)
{
    /* assumes that it passed is_sinit_acmod() */

    acm_info_table_t *info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL || info_table->version < 3 )
        return 0;

    return info_table->capabilities._raw;
}

static bool are_sizes_equal_pad_adjusted(uint32_t acmod_size, acm_hdr_t *acm_hdr)
{
    /* Sizes are equal, so no padding */
    if ( acmod_size == (acm_hdr->size * 4) ) {
        return true;
    }

    /* Padding can't be negative */
    if ( acmod_size < (acm_hdr->size * 4) ) {
        return false;
    }

    /* Check if padding is in allowed range */
    if ( (acmod_size - (acm_hdr->size * 4) >= ACM_SIZE_MIN_PADDING) &&
         (acmod_size - (acm_hdr->size * 4) <= ACM_SIZE_MAX_PADDING) ) {
        printf("\t acmod_size=%x, != acm_hdr->size*4=%x"
               ", padding present (assuming 0x%x padding)\n",
               acmod_size, acm_hdr->size * 4, acmod_size - (acm_hdr->size * 4));
        return true;
    }

    return false;
}

static bool is_acmod(const void *acmod_base, uint32_t acmod_size, uint8_t *type, bool quiet)
{
    acm_hdr_t *acm_hdr = (acm_hdr_t *)acmod_base;
    acm_info_table_t *info_table;

    /* first check size */
    if ( acmod_size < sizeof(acm_hdr_t) ) {
        if ( !quiet )
            printf("\t ACM size is too small: acmod_size=%x,"
                   " sizeof(acm_hdr_t)=%x\n", acmod_size,
                   (uint32_t)sizeof(acm_hdr_t) );
        return false;
    }

    /* then check overflow */
    if ( multiply_overflow_u32(acm_hdr->size, 4) ) {
        if ( !quiet )
            printf("\t ACM header size in bytes overflows\n");
        return false;
    }

    /* then check size equivalency */
    if ( !are_sizes_equal_pad_adjusted(acmod_size, acm_hdr) ) {
        if ( !quiet )
            printf("\t ACM size mismatch: acmod_size=%x,"
                   " acm_hdr->size*4=%x\n", acmod_size, acm_hdr->size*4);
        return false;
    }

    /* then check type and vendor */
    if ( (acm_hdr->module_type != ACM_TYPE_CHIPSET) ||
         (acm_hdr->module_vendor != ACM_VENDOR_INTEL) ) {
        if ( !quiet )
            printf("\t ACM type/vendor mismatch: module_type=%x,"
                   " module_vendor=%x\n", acm_hdr->module_type,
                   acm_hdr->module_vendor);
        return false;
    }

    info_table = get_acmod_info_table(acm_hdr);
    if ( info_table == NULL )
        return false;

    /* check if ACM UUID is present */
    if ( !are_uuids_equal(&(info_table->uuid), &((uuid_t)ACM_UUID_V3)) ) {
        if ( !quiet ) {
            printf("\t unknown UUID: "); print_uuid(&info_table->uuid);
            printf("\n");
        }
        return false;
    }

    if ( type != NULL )
        *type = info_table->chipset_acm_type;

    if ( info_table->version < 3 ) {
        if ( !quiet )
            printf("\t ACM info_table version unsupported (%u)\n",
                   (uint32_t)info_table->version);
        return false;
    }
    /* there is forward compatibility, so this is just a warning */
    else if ( info_table->version > 7 ) {
        if ( !quiet )
            printf("\t ACM info_table version mismatch (%u)\n",
                   (uint32_t)info_table->version);
    }

    return true;
}

bool is_racm_acmod(const void *acmod_base, uint32_t acmod_size, bool quiet)
{
    uint8_t type;

    if ( !is_acmod(acmod_base, acmod_size, &type, quiet) )
        return false;

    if ( type != ACM_CHIPSET_TYPE_BIOS_REVOC &&
         type != ACM_CHIPSET_TYPE_SINIT_REVOC ) {
        printf("ACM is not an revocation ACM (%x)\n", type);
        return false;
    }

    if ( acmod_size != 0x8000 && acmod_size != 0x10000 ) {
        printf("ACM is not an RACM, bad size (0x%x)\n", acmod_size);
        return false;
    }

    return true;
}

bool is_sinit_acmod(const void *acmod_base, uint32_t acmod_size, bool quiet)
{
    uint8_t type;

    if ( !is_acmod(acmod_base, acmod_size, &type, quiet) )
        return false;

    if ( type != ACM_CHIPSET_TYPE_SINIT ) {
        printf("ACM is not an SINIT ACM (%x)\n", type);
        return false;
    }

    return true;
}

bool does_acmod_match_platform(const acm_hdr_t* hdr)
{
    /* used to ensure we don't print chipset/proc info for each module */
    static bool printed_host_info;
    txt_heap_t *txt_heap;
    bios_data_t *bios_data;
    txt_didvid_t didvid;
    txt_ver_fsbif_qpiif_t ver;
    uint64_t platform_id;
    uint32_t fms;
    acm_chipset_id_list_t *chipset_id_list;
    unsigned int i;

    /* this fn assumes that the ACM has already passed the is_acmod() checks */
    acm_info_table_t *info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL )
        return false;

    /* verify client/server platform match */
    txt_heap = get_txt_heap();
    bios_data = get_bios_data_start(txt_heap);
    if (info_table->version >= 5 && bios_data->version >= 6) {
        uint32_t bios_type = bios_data->flags.bits.mle.platform_type;
        uint32_t sinit_type = info_table->capabilities.platform_type;

        if (bios_type == PLATFORM_TYPE_CLIENT && sinit_type != PLATFORM_TYPE_CLIENT) {
            printf("Error: Non-client ACM on client platform\n");
            return false;
        }

        if (bios_type == PLATFORM_TYPE_SERVER && sinit_type != PLATFORM_TYPE_SERVER) {
            printf("Error: Non-server ACM on server platform\n");
            return false;
        }
    }

    /* get chipset fusing, device, and vendor id info */
    didvid._raw = read_pub_config_reg(TXTCR_DIDVID);
    ver._raw = read_pub_config_reg(TXTCR_VER_FSBIF);
    if ( (ver._raw & 0xffffffff) == 0xffffffff ||
         (ver._raw & 0xffffffff) == 0x00 )         /* need to use VER.QPIIF */
        ver._raw = read_pub_config_reg(TXTCR_VER_QPIIF);
    if ( !printed_host_info ) {
        printf("chipset production fused: %x\n", ver.prod_fused );
        printf("chipset ids: vendor: 0x%x, device: 0x%x, revision: 0x%x\n",
               didvid.vendor_id, didvid.device_id, didvid.revision_id);
    }

    /* get processor family/model/stepping and platform ID */
    fms = cpuid_eax(1);
    platform_id = rdmsr64(IA32_PLATFORM_ID);
    if ( !printed_host_info ) {
        printf("processor family/model/stepping: 0x%x\n", fms );
        printf("platform id: 0x%llx\n", (unsigned long long)platform_id);
    }
    printed_host_info = true;

    /*
     * check if chipset fusing is same
     */
    if ( ver.prod_fused != !hdr->flags.debug_signed ) {
        printf("\t production/debug mismatch between chipset and ACM\n");
        return false;
    }

    /*
     * check if chipset vendor/device/revision IDs match
     */
    chipset_id_list = get_acmod_chipset_list(hdr);
    if ( chipset_id_list == NULL )
        return false;

    printf("\t %x ACM chipset id entries:\n", chipset_id_list->count);
    for ( i = 0; i < chipset_id_list->count; i++ ) {
        acm_chipset_id_t *chipset_id = &(chipset_id_list->chipset_ids[i]);
        printf("\t     vendor: 0x%x, device: 0x%x, flags: 0x%x, "
               "revision: 0x%x, extended: 0x%x\n",
               (uint32_t)chipset_id->vendor_id,
               (uint32_t)chipset_id->device_id, chipset_id->flags,
               (uint32_t)chipset_id->revision_id, chipset_id->extended_id);

        if ( (didvid.vendor_id == chipset_id->vendor_id ) &&
             (didvid.device_id == chipset_id->device_id ) &&
             ( ( ( (chipset_id->flags & 0x1) == 0) &&
                 (didvid.revision_id == chipset_id->revision_id) ) ||
               ( ( (chipset_id->flags & 0x1) == 1) &&
                 ( (didvid.revision_id & chipset_id->revision_id) != 0 ) ) ) )
            break;
    }
    if ( i >= chipset_id_list->count ) {
        printf("\t chipset id mismatch\n");
        return false;
    }

    /*
     * check if processor family/model/stepping and platform IDs match
     */
    if ( info_table->version >= 4 ) {
        acm_processor_id_list_t *proc_id_list = get_acmod_processor_list(hdr);
        if ( proc_id_list == NULL )
            return false;

        printf("\t %x ACM processor id entries:\n", proc_id_list->count);
        for ( i = 0; i < proc_id_list->count; i++ ) {
            acm_processor_id_t *proc_id = &(proc_id_list->processor_ids[i]);
            printf("\t     fms: 0x%x, fms_mask: 0x%x, platform_id: 0x%llx, "
                   "platform_mask: 0x%llx\n",
                   proc_id->fms, proc_id->fms_mask,
                   (unsigned long long)proc_id->platform_id,
                   (unsigned long long)proc_id->platform_mask);

            if ( (proc_id->fms == (fms & proc_id->fms_mask)) &&
                 (proc_id->platform_id == (platform_id & proc_id->platform_mask))
               )
                break;
        }
        if ( i >= proc_id_list->count ) {
            printf("\t processor mismatch\n");
            return false;
        }
    }

    return true;
}

acm_hdr_t *get_bios_sinit(const void *sinit_region_base)
{
    txt_heap_t *txt_heap;
    bios_data_t *bios_data;

    if ( sinit_region_base == NULL )
       return NULL;
    txt_heap = get_txt_heap();
    bios_data = get_bios_data_start(txt_heap);

    if ( bios_data->bios_sinit_size == 0 )
        return NULL;

    /* BIOS has loaded an SINIT module, so verify that it is valid */
    printf("BIOS has already loaded an SINIT module\n");

    /* is it a valid SINIT module? */
    if ( !is_sinit_acmod(sinit_region_base, bios_data->bios_sinit_size, false) ||
         !does_acmod_match_platform((acm_hdr_t *)sinit_region_base) )
        return NULL;

    return (acm_hdr_t *)sinit_region_base;
}

// XMHF: Remove RACM functions.
//static void *alloc_racm_region(uint32_t size)
//{
//    /* TODO: find a real unused memory place through mbi */
//    return (void *)(long)(0x2000000 + size - size); /* 32M */
//}
//
//acm_hdr_t *copy_racm(const acm_hdr_t *racm)
//{
//    /* find a 32KB aligned memory */
//    uint32_t racm_region_size = racm->size*4;
//    void *racm_region_base = alloc_racm_region(racm_region_size);
//    printf("RACM.BASE: %p\n", racm_region_base);
//    printf("RACM.SIZE: 0x%x (%u)\n", racm_region_size, racm_region_size);
//
//    /* copy it there */
//    memcpy(racm_region_base, racm, racm->size*4);
//
//    printf("copied RACM (size=%x) to %p\n", racm->size*4,
//           racm_region_base);
//
//    return (acm_hdr_t *)racm_region_base;
//}

acm_hdr_t *copy_sinit(const acm_hdr_t *sinit)
{
    /* get BIOS-reserved region from TXT.SINIT.BASE config reg */
    void *sinit_region_base =
        (void*)(unsigned long)read_pub_config_reg(TXTCR_SINIT_BASE);
    uint32_t sinit_region_size = (uint32_t)read_pub_config_reg(TXTCR_SINIT_SIZE);
    acm_hdr_t *bios_sinit;
    printf("TXT.SINIT.BASE: %p\n", sinit_region_base);
    printf("TXT.SINIT.SIZE: 0x%x (%u)\n", sinit_region_size, sinit_region_size);

    /*
     * check if BIOS already loaded an SINIT module there
     */
    bios_sinit = get_bios_sinit(sinit_region_base);
    if ( bios_sinit != NULL ) {
        /* no other SINIT was provided so must use one BIOS provided */
        if ( sinit == NULL ) {
            printf("no SINIT provided by bootloader; using BIOS SINIT\n");
            return bios_sinit;
        }

        /* is it newer than the one we've been provided? */
        if ( bios_sinit->date >= sinit->date ) {
            printf("BIOS-provided SINIT is newer, so using it\n");
            return bios_sinit;    /* yes */
        }
        else
            printf("BIOS-provided SINIT is older: date=%x\n", bios_sinit->date);
    }
    /* our SINIT is newer than BIOS's (or BIOS did not have one) */

    /* BIOS SINIT not present or not valid and none provided */
    if ( sinit == NULL )
        return NULL;

    /* overflow? */
    if ( multiply_overflow_u32(sinit->size, 4) ) {
        printf("sinit size in bytes overflows\n");
        return NULL;
    }

    /* make sure our SINIT fits in the reserved region */
    if ( (sinit->size * 4) > sinit_region_size ) {
        printf("BIOS-reserved SINIT size (%x) is too small for loaded "
               "SINIT (%x)\n", sinit_region_size, sinit->size*4);
        return NULL;
    }

    if ( sinit_region_base == NULL )
       return NULL;

    /* copy it there */
    memcpy(sinit_region_base, sinit, sinit->size*4);

    printf("copied SINIT (size=%x) to %p\n", sinit->size*4,
           sinit_region_base);

    return (acm_hdr_t *)sinit_region_base;
}

// XMHF: Remove RACM functions.
//bool verify_racm(const acm_hdr_t *acm_hdr)
//{
//    getsec_parameters_t params;
//    uint32_t size;
//
//    /* assumes this already passed is_acmod() test */
//
//    size = acm_hdr->size * 4;        /* hdr size is in dwords, we want bytes */
//
//    /*
//     * AC mod must start on 4k page boundary
//     */
//
//    if ( (unsigned long)acm_hdr & 0xfff ) {
//        printf("AC mod base not 4K aligned (%p)\n", acm_hdr);
//        return false;
//    }
//    printf("AC mod base alignment OK\n");
//
//    /* AC mod size must:
//     * - be multiple of 64
//     * - greater than ???
//     * - less than max supported size for this processor
//     */
//
//    if ( (size == 0) || ((size % 64) != 0) ) {
//        printf("AC mod size %x bogus\n", size);
//        return false;
//    }
//
//    if ( !get_parameters(&params) ) {
//        printf("get_parameters() failed\n");
//        return false;
//    }
//
//    if ( size > params.acm_max_size ) {
//        printf("AC mod size too large: %x (max=%x)\n", size,
//               params.acm_max_size);
//        return false;
//    }
//
//    printf("AC mod size OK\n");
//
//    /*
//     * perform checks on AC mod structure
//     */
//
//    /* print it for debugging */
//    print_acm_hdr(acm_hdr, "RACM");
//
//    /* entry point is offset from base addr so make sure it is within module */
//    if ( acm_hdr->entry_point >= size ) {
//        printf("AC mod entry (%08x) >= AC mod size (%08x)\n",
//               acm_hdr->entry_point, size);
//        return false;
//    }
//
//    /* overflow? */
//    if ( plus_overflow_u32(acm_hdr->seg_sel, 8) ) {
//        printf("seg_sel plus 8 overflows\n");
//        return false;
//    }
//
//    if ( !acm_hdr->seg_sel           ||       /* invalid selector */
//         (acm_hdr->seg_sel & 0x07)   ||       /* LDT, PL!=0 */
//         (acm_hdr->seg_sel + 8 > acm_hdr->gdt_limit) ) {
//        printf("AC mod selector [%04x] bogus\n", acm_hdr->seg_sel);
//        return false;
//    }
//
//    return true;
//}

// XMHF: TODO: Commented verify_IA32_se_svn_status().
#if 0
/*
 * Do some AC module sanity checks because any violations will cause
 * an TXT.RESET.  Instead detect these, print a desriptive message,
 * and skip SENTER/ENTERACCS
 */
void verify_IA32_se_svn_status(const acm_hdr_t *acm_hdr)
{
    struct tpm_if *tpm = get_tpm();
    const struct tpm_if_fp *tpm_fp = get_tpm_fp();

    printf("SGX:verify_IA32_se_svn_status is called\n");

    //check if SGX is enabled by cpuid with ax=7, cx=0
    if ((cpuid_ebx1(7,0) & 0x00000004) == 0){
        printf("SGX is not enabled, cpuid.ebx: 0x%x\n", cpuid_ebx1(7,0));
        return;
    }
    printf("SGX is enabled, cpuid.ebx:0x%x\n", cpuid_ebx1(7,0));
    printf("Comparing se_svn with ACM Header se_svn\n");

    if (((rdmsr64(MSR_IA32_SE_SVN_STATUS)>>16) & 0xff) != acm_hdr->se_svn) {
        printf("se_svn is not equal to ACM se_svn\n");
        if (!tpm_fp->nv_write(tpm, 0, tpm->sgx_svn_index, 0, (uint8_t *)&(acm_hdr->se_svn), 1))
            printf("Write sgx_svn_index 0x%x failed. \n", tpm->sgx_svn_index);
        else
            printf("Write sgx_svn_index with 0x%x successful.\n", acm_hdr->se_svn);

        if ((rdmsr64(MSR_IA32_SE_SVN_STATUS) & 0X00000001) !=0)  /* reset platform */
        // printf("SGX:A reset is required in this boot\n");
           outb(0xcf9, 0x06);
    }
    else
        printf("se_svn is equal to ACM se_svn\n");

}
#endif

bool verify_acmod(const acm_hdr_t *acm_hdr)
{
    // XMHF: Remove check of params.acm_max_size in verify_acmod().
    //getsec_parameters_t params;
    uint32_t size;
    acm_info_table_t *info_table;
    txt_caps_t caps_mask = { 0 };

    /* assumes this already passed is_acmod() test */

    size = acm_hdr->size * 4;        /* hdr size is in dwords, we want bytes */

    /*
     * AC mod must start on 4k page boundary
     */

    if ( (unsigned long)acm_hdr & 0xfff ) {
        printf("AC mod base not 4K aligned (%p)\n", acm_hdr);
        return false;
    }
    printf("AC mod base alignment OK\n");

    /* AC mod size must:
     * - be multiple of 64
     * - greater than ???
     * - less than max supported size for this processor
     */

    if ( (size == 0) || ((size % 64) != 0) ) {
        printf("AC mod size %x bogus\n", size);
        return false;
    }

    // XMHF: Remove check of params.acm_max_size in verify_acmod().
    //if ( !get_parameters(&params) ) {
    //    printf("get_parameters() failed\n");
    //    return false;
    //}
    //
    //if ( size > params.acm_max_size ) {
    //    printf("AC mod size too large: %x (max=%x)\n", size,
    //           params.acm_max_size);
    //    return false;
    //}

    printf("AC mod size OK\n");

    /*
     * perform checks on AC mod structure
     */

    /* print it for debugging */
    print_acm_hdr(acm_hdr, "SINIT");

    /* entry point is offset from base addr so make sure it is within module */
    if ( acm_hdr->entry_point >= size ) {
        printf("AC mod entry (%08x) >= AC mod size (%08x)\n",
               acm_hdr->entry_point, size);
        return false;
    }

    /* overflow? */
    if ( plus_overflow_u32(acm_hdr->seg_sel, 8) ) {
        printf("seg_sel plus 8 overflows\n");
        return false;
    }

    if ( !acm_hdr->seg_sel           ||       /* invalid selector */
         (acm_hdr->seg_sel & 0x07)   ||       /* LDT, PL!=0 */
         (acm_hdr->seg_sel + 8 > acm_hdr->gdt_limit) ) {
        printf("AC mod selector [%04x] bogus\n", acm_hdr->seg_sel);
        return false;
    }

    /*
     * check for compatibility with this MLE
     */

    info_table = get_acmod_info_table(acm_hdr);
    if ( info_table == NULL )
        return false;

    /* check MLE header versions */
    if ( info_table->min_mle_hdr_ver > MLE_HDR_VER ) {
        printf("AC mod requires a newer MLE (0x%08x)\n",
               info_table->min_mle_hdr_ver);
        return false;
    }

    /* check capabilities */
    /* we need to match one of rlp_wake_{getsec, monitor} */
    caps_mask.rlp_wake_getsec = caps_mask.rlp_wake_monitor = 1;

    if ( ( ( MLE_HDR_CAPS & caps_mask._raw ) &
           ( info_table->capabilities._raw & caps_mask._raw) ) == 0 ) {
        printf("SINIT and MLE not support compatible RLP wake mechanisms\n");
        return false;
    }
    /* we also expect ecx_pgtbl to be set */
    if ( !info_table->capabilities.ecx_pgtbl ) {
        printf("SINIT does not support launch with MLE pagetable in ECX\n");
        /* TODO when SINIT ready
         * return false;
         */
    }

    /* check for version of OS to SINIT data */
    /* we don't support old versions */
    if ( info_table->os_sinit_data_ver < MIN_OS_SINIT_DATA_VER ) {
        printf("SINIT's os_sinit_data version unsupported (%u)\n",
               info_table->os_sinit_data_ver);
        return false;
    }
    /* only warn if SINIT supports more recent version than us */
    else if ( info_table->os_sinit_data_ver > MAX_OS_SINIT_DATA_VER ) {
        printf("SINIT's os_sinit_data version unsupported (%u)\n",
               info_table->os_sinit_data_ver);
    }

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
