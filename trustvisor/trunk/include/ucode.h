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

#ifndef _UCODE_H_
#define _UCODE_H_

#include <types.h>

/*
 * Definitions for 'bool' type
 */
#define bool    _Bool
#define true    1
#define false   0

#define UCODE_MAGIC 0x00414d44 /* AMD microcode */
#define UCODE_EQUTAB            0
#define UCODE_PATCH             1

struct ucode_container_hdr {
    uint32_t    type;
    uint32_t    size;
};

struct ucode_equ_entry {
    uint32_t    installed_cpu;
    uint32_t    fixed_errata_mask;
    uint32_t    fixed_errata_compare;
    uint32_t    equiv_cpu;
};

struct ucode_patch_hdr {
    uint32_t    data_code;
    uint32_t    patch_id;
    uint16_t    mc_patch_data_id;
    uint8_t     mc_patch_data_len;
    uint8_t     init_flag;
    uint32_t    mc_patch_data_checksum;
    uint32_t    nb_dev_id;
    uint32_t    sb_dev_id;
    uint16_t    processor_rev_id;
    uint8_t     nb_rev_id;
    uint8_t     sb_rev_id;
    uint8_t     bios_api_rev;
    uint8_t     reserved1[3];
    uint32_t    match_reg[8];
};

typedef enum { CLEAR_MICROCODE, LOAD_MICROCODE } wakeup_state_t;

extern wakeup_state_t ap_wakeup_state;

extern bool init_all_aps(void);
extern bool start_all_aps(void);

/* extern bool dev_error(void); */
/* extern void enable_dev(void); */
/* extern void disable_dev(void); */
/* extern void dev_block(void *addr, uint32_t size); */
/* extern bool dev_init(multiboot_info_t *mbi); */

/* extern bool amd_nb_init(void); */
/* extern void amd_nb_fini(void); */

extern bool clear_microcode(void);
extern bool core_load_ucode(u32 ucode_addr);


/* extern void welcome(void); */
/* extern void error(void); */

extern void putstr(const char* str);
extern void putbytes(u8 *bytes, int len);
extern void init_uart(void);

#endif
