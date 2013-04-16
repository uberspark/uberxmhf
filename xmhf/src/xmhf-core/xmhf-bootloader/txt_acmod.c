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
 * acmod.c: support functions for use of Intel(r) TXT Authenticated
 *          Code (AC) Modules
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

static acm_info_table_t *get_acmod_info_table(acm_hdr_t* hdr)
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

static acm_chipset_id_list_t *get_acmod_chipset_list(acm_hdr_t* hdr)
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
    if ( plus_overflow_u32(id_list_off, sizeof(acm_chipset_id_t)) ) {
        printf("id_list_off plus acm_chipset_id_t size overflows\n");
        return NULL;
    }

    /* check that chipset id table is w/in ACM */
    if ( id_list_off + sizeof(acm_chipset_id_t) > size ) {
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
    if ( plus_overflow_u32(id_list_off + sizeof(acm_chipset_id_t),
        chipset_id_list->count * sizeof(acm_chipset_id_t)) ) {
        printf("size of all entries overflows\n");
        return NULL;
    }

    /* check that all entries are w/in ACM */
    if ( id_list_off + sizeof(acm_chipset_id_t) +
         chipset_id_list->count * sizeof(acm_chipset_id_t) > size ) {
        printf("ACM chipset id entries are too big:"
               " chipset_id_list->count=%x\n", chipset_id_list->count);
        return NULL;
    }

    return chipset_id_list;
}

void print_txt_caps(const char *prefix, txt_caps_t caps)
{
    printf("%scapabilities: 0x%08x\n", prefix, caps._raw);
    printf("%s    rlp_wake_getsec: %d\n", prefix, caps.rlp_wake_getsec);
    printf("%s    rlp_wake_monitor: %d\n", prefix, caps.rlp_wake_monitor);
    printf("%s    ecx_pgtbl: %d\n", prefix, caps.ecx_pgtbl);
}

/* UUID helpers from tboot-20101005/include/uuid.h */
void print_uuid(const uuid_t *uuid)
{
    printf("{0x%08x, 0x%04x, 0x%04x, 0x%04x,\n"
           "\t\t{0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x}}",
           uuid->data1, (uint32_t)uuid->data2, (uint32_t)uuid->data3,
           (uint32_t)uuid->data4, (uint32_t)uuid->data5[0],
           (uint32_t)uuid->data5[1], (uint32_t)uuid->data5[2],
           (uint32_t)uuid->data5[3], (uint32_t)uuid->data5[4],
           (uint32_t)uuid->data5[5]);
}

static inline bool are_uuids_equal(const uuid_t *uuid1, const uuid_t *uuid2)
{
    return (memcmp((const char *)uuid1, (const char *)uuid2, sizeof(*uuid1)) == 0);
}

static void print_acm_hdr(acm_hdr_t *hdr, const char *mod_name)
{
    acm_info_table_t *info_table;
    acm_chipset_id_list_t *chipset_id_list;
    unsigned int i;
    
    printf("AC module header dump for %s:\n",
           (mod_name == NULL) ? "?" : mod_name);

    /* header */
    printf("\t type: 0x%x ", hdr->module_type);
    if ( hdr->module_type == ACM_TYPE_CHIPSET )
        printf("(ACM_TYPE_CHIPSET)\n");
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
    printf("\t code_control: 0x%x\n", hdr->code_control);
    printf("\t error_entry_point: 0x%x\n", hdr->error_entry_point);
    printf("\t gdt_limit 0x%x, gdt_base 0x%x\n", hdr->gdt_limit,
           hdr->gdt_base);
    printf("\t entry point (seg_sel:entry_point): 0x%08x:%08x\n", hdr->seg_sel,
           hdr->entry_point);
    printf("\t scratch_size: 0x%x (%u)", hdr->scratch_size,
           hdr->scratch_size);

    /* GDT */
    print_hex("\t\t SINIT GDT: ", (void *)((u32)hdr+hdr->gdt_base), hdr->gdt_limit);
    /* info table */
    printf("\t info_table:\n");
    info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL ) {
        printf("\t\t <invalid>\n");
        return;
    }
    printf("\t\t uuid: "); print_uuid(&info_table->uuid); printf("\n");
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

    /* chipset list */
    printf("\t chipset list:\n");
    chipset_id_list = get_acmod_chipset_list(hdr);
    if ( chipset_id_list == NULL ) {
        printf("\t\t <invalid>\n");
        return;
    }
    printf("\t\t count: %u\n", chipset_id_list->count);
    for ( i = 0; i < chipset_id_list->count; i++ ) {
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
}

uint32_t get_supported_os_sinit_data_ver(acm_hdr_t* hdr)
{
    /* assumes that it passed is_sinit_acmod() */

    acm_info_table_t *info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL )
        return 0;

    return info_table->os_sinit_data_ver;
}

// return type changed from txt_caps_t due to -Waggregate-return
uint32_t get_sinit_capabilities(acm_hdr_t* hdr)
{
    /* assumes that it passed is_sinit_acmod() */

    acm_info_table_t *info_table = get_acmod_info_table(hdr);
    if ( info_table == NULL || info_table->version < 3 )
        return 0;

    return info_table->capabilities._raw;
}

static bool is_acmod(void *acmod_base, size_t acmod_size, uint8_t *type,
                     bool quiet)
{
    acm_hdr_t *acm_hdr;
    acm_info_table_t *info_table;

    acm_hdr = (acm_hdr_t *)acmod_base;

    /* first check size */
    if ( acmod_size < sizeof(acm_hdr_t) ) {
        if ( !quiet )
            printf("\t ACM size is too small: acmod_size=%x,"
                   " sizeof(acm_hdr)=%x\n", (uint32_t)acmod_size,
                   (uint32_t)sizeof(acm_hdr) );
        return false;
    }

    /* then check overflow */
    if ( multiply_overflow_u32(acm_hdr->size, 4) ) {
        if ( !quiet )
            printf("\t ACM header size in bytes overflows\n");
        return false;
    }

    /* then check size equivalency */
    if ( acmod_size != acm_hdr->size * 4 ) {
        if ( !quiet )
            printf("\t ACM size is too small: acmod_size=%x,"
                   " acm_hdr->size*4=%x\n", (uint32_t)acmod_size,
                   acm_hdr->size*4);
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
    else if ( info_table->version > 3 ) {
        if ( !quiet )
            printf("\t ACM info_table version mismatch (%u)\n",
                   (uint32_t)info_table->version);
    }

    return true;
}

bool is_sinit_acmod(void *acmod_base, size_t acmod_size, bool quiet)
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

bool does_acmod_match_chipset(acm_hdr_t* hdr)
{
    /* this fn assumes that the ACM has already passed the is_acmod() checks */
    acm_chipset_id_list_t *chipset_id_list;
    txt_didvid_t didvid;
    unsigned int i;
    /*
     * check if fusing is same
     */
    txt_ver_fsbif_emif_t ver;
    ver._raw = read_pub_config_reg(TXTCR_VER_FSBIF);
    if ( (ver._raw & 0xffffffff) == 0xffffffff ||
         (ver._raw & 0xffffffff) == 0x00 )         /* need to use VER.EMIF */
        ver._raw = read_pub_config_reg(TXTCR_VER_EMIF);
    if ( ver.prod_fused != !hdr->flags.debug_signed ) {
        printf("\t production/debug mismatch between chipset and ACM\n");
        return false;
    }

    /*
     * check if vendor/device/revision IDs match
     */
    chipset_id_list = get_acmod_chipset_list(hdr);
    if ( chipset_id_list == NULL )
        return false;

    /* get chipset device and vendor id info */
    didvid._raw = read_pub_config_reg(TXTCR_DIDVID);

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
                 ((didvid.revision_id & chipset_id->revision_id) != 0 ) ) ) )
            return true;
    }

    printf("\t ACM does not match chipset\n");

    return false;
}

acm_hdr_t *copy_sinit(acm_hdr_t *sinit)
{
    void *sinit_region_base;
    uint32_t sinit_region_size;
    txt_heap_t *txt_heap;
    bios_data_t *bios_data;

    /* get BIOS-reserved region from LT.SINIT.BASE config reg */
    sinit_region_base =
        (void*)(unsigned long)read_pub_config_reg(TXTCR_SINIT_BASE);
    sinit_region_size = (uint32_t)read_pub_config_reg(TXTCR_SINIT_SIZE);

    /*
     * check if BIOS already loaded an SINIT module there
     */
    txt_heap = get_txt_heap();
    bios_data = get_bios_data_start(txt_heap);
    /* BIOS has loaded an SINIT module, so verify that it is valid */
    if ( bios_data->bios_sinit_size != 0 ) {
        printf("BIOS has already loaded an SINIT module\n");
        /* is it a valid SINIT module? */
        if ( is_sinit_acmod(sinit_region_base, bios_data->bios_sinit_size, false) &&
             does_acmod_match_chipset((acm_hdr_t *)sinit_region_base) ) {
            /* no other SINIT was provided so must use one BIOS provided */
            if ( sinit == NULL )
                return (acm_hdr_t *)sinit_region_base;

            /* is it newer than the one we've been provided? */
            if ( ((acm_hdr_t *)sinit_region_base)->date >= sinit->date ) {
                printf("BIOS-provided SINIT is newer, so using it\n");
                return (acm_hdr_t *)sinit_region_base;    /* yes */
            }
            else
                printf("BIOS-provided SINIT is older: date=%x\n",
                       ((acm_hdr_t *)sinit_region_base)->date);
        }
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

    /* copy it there */
    memcpy(sinit_region_base, sinit, sinit->size*4);

    printf("copied SINIT (size=%x) to %p\n", sinit->size*4,
           sinit_region_base);

    return (acm_hdr_t *)sinit_region_base;
}


/*
 * Do some AC module sanity checks because any violations will cause
 * an TXT.RESET.  Instead detect these, print a desriptive message,
 * and skip SENTER/ENTERACCS
 */
bool verify_acmod(acm_hdr_t *acm_hdr)
{
    getsec_parameters_t params;
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

    /// XXX TODO bring in txt.c stuff
/*     if ( !get_parameters(&params) ) { */
/*         printf("get_parameters() failed\n"); */
/*         return false; */
/*     } */

    if ( size > params.acm_max_size ) {
        printf("AC mod size too large: %x (max=%x)\n", size,
               params.acm_max_size);
        return false;
    }

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
    if ( info_table->os_sinit_data_ver < 4 ) {
        printf("SINIT's os_sinit_data version unsupported (%u)\n",
               info_table->os_sinit_data_ver);
        return false;
    }
    /* only warn if SINIT supports more recent version than us */
    else if ( info_table->os_sinit_data_ver > 5 ) {
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
