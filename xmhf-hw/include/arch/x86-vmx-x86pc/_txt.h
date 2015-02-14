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

/* txt.h - Unified header file for Intel TXT requirements */
//author: jonmccune@cmu.edu

#ifndef __UNI_TXT_
#define __UNI_TXT_

#ifndef __ASSEMBLY__

//#include "_txt_config_regs.h"

/*
 * TXT configuration registers (offsets from TXT_{PUB, PRIV}_CONFIG_REGS_BASE)
 */

#define TXT_PUB_CONFIG_REGS_BASE       0xfed30000
#define TXT_PRIV_CONFIG_REGS_BASE      0xfed20000

/* # pages for each config regs space - used by fixmap */
#define NR_TXT_CONFIG_PAGES            ((TXT_PUB_CONFIG_REGS_BASE - \
                                        TXT_PRIV_CONFIG_REGS_BASE) >>    \
                                        PAGE_SHIFT)

/* offsets to config regs (from either public or private _BASE) */
#define TXTCR_STS                   0x0000
#define TXTCR_ESTS                  0x0008
#define TXTCR_ERRORCODE             0x0030
#define TXTCR_CMD_RESET             0x0038
#define TXTCR_CMD_CLOSE_PRIVATE     0x0048
#define TXTCR_VER_FSBIF             0x0100
#define TXTCR_DIDVID                0x0110
#define TXTCR_VER_EMIF              0x0200
#define TXTCR_CMD_UNLOCK_MEM_CONFIG 0x0218
#define TXTCR_SINIT_BASE            0x0270
#define TXTCR_SINIT_SIZE            0x0278
#define TXTCR_MLE_JOIN              0x0290
#define TXTCR_HEAP_BASE             0x0300
#define TXTCR_HEAP_SIZE             0x0308
#define TXTCR_MSEG_BASE             0x0310
#define TXTCR_MSEG_SIZE             0x0318
#define TXTCR_DPR                   0x0330
#define TXTCR_CMD_OPEN_LOCALITY1    0x0380
#define TXTCR_CMD_CLOSE_LOCALITY1   0x0388
#define TXTCR_CMD_OPEN_LOCALITY2    0x0390
#define TXTCR_CMD_CLOSE_LOCALITY2   0x0398
#define TXTCR_CMD_SECRETS           0x08e0
#define TXTCR_CMD_NO_SECRETS        0x08e8
#define TXTCR_E2STS                 0x08f0

/*
 * format of ERRORCODE register
 */
typedef union {
    uint64_t _raw;
    struct {
        uint64_t   type       : 30;    /* external-specific error code */
        uint64_t   external   : 1;     /* 0=from proc, 1=from external SW */
        uint64_t   valid      : 1;     /* 1=valid */
    };
} txt_errorcode_t;

/*
 * format of ESTS register
 */
typedef union {
    uint64_t _raw;
    struct {
        uint64_t   txt_reset_sts      : 1;
        uint64_t   reserved1          : 5;
        uint64_t   txt_wake_error_sts : 1;
        uint64_t   reserved2          : 1;
    };
} txt_ests_t;

/*
 * format of E2STS register
 */
typedef union {
    uint64_t _raw;
    struct {
        uint64_t   slp_entry_error_sts  : 1;
        uint64_t   secrets_sts          : 1;
        uint64_t   block_mem_sts        : 1;
        uint64_t   reset_sts            : 1;
    };
} txt_e2sts_t;

/*
 * format of STS register
 */
typedef union {
    uint64_t _raw;
    struct {
        uint64_t   senter_done_sts         : 1;
        uint64_t   sexit_done_sts          : 1;
        uint64_t   reserved1               : 2;
        uint64_t   mem_unlock_sts          : 1;
        uint64_t   reserved2               : 1;
        uint64_t   mem_config_lock_sts     : 1;
        uint64_t   private_open_sts        : 1;
        uint64_t   reserved3               : 3;
        uint64_t   mem_config_ok_sts       : 1;
    };
} txt_sts_t;

/*
 * format of DIDVID register
 */
typedef union {
    uint64_t _raw;
    struct {
        uint16_t  vendor_id;
        uint16_t  device_id;
        uint16_t  revision_id;
        uint16_t  reserved;
    };
} txt_didvid_t;

/*
 * format of VER.FSBIF and VER.EMIF registers
 */
typedef union {
    uint64_t _raw;
    struct {
        uint64_t  reserved       : 31;
        uint64_t  prod_fused     : 1;
    };
} txt_ver_fsbif_emif_t;

/*
 * format of DPR register
 */
typedef union {
    uint64_t _raw;
    struct {
        uint64_t  lock           : 1;
        uint64_t  reserved1      : 3;
        uint64_t  size           : 8;
        uint64_t  reserved2      : 8;
        uint64_t  top            : 12;
        uint64_t  reserved3      : 32;
    };
} txt_dpr_t;

/*
 * RLP JOIN structure for GETSEC[WAKEUP] and MLE_JOIN register
 */
typedef struct {
    uint32_t	gdt_limit;
    uint32_t	gdt_base;
    uint32_t	seg_sel;               /* cs (ds, es, ss are seg_sel+8) */
    uint32_t	entry_point;           /* phys addr */
} mle_join_t;

/*
 * format of MSEG header
 */
typedef struct {
    uint32_t    revision_id;
    uint32_t    smm_mon_feat;
    uint32_t    gdtr_limit;
    uint32_t    gdtr_base_offset;
    uint32_t    cs_sel;
    uint32_t    eip_offset;
    uint32_t    esp_offset;
    uint32_t    cr3_offset;
} mseg_hdr_t;

/*
 * fns to read/write TXT config regs
 *
 * NOTE: MODIFIED TO ALWAYS USE %FS SEGMENT-OVERRIDE
 */

static inline uint64_t read_config_reg(uint32_t config_regs_base, uint32_t reg)
{
    /* these are MMIO so make sure compiler doesn't optimize */
    //return *(volatile uint64_t *)(unsigned long)(config_regs_base +
    //reg);

    u64 ret;
    u32 addr = config_regs_base + reg;
    __asm__ __volatile__("movl %%fs:(%%ebx), %%eax\r\n"
                         "movl %%fs:4(%%ebx), %%edx\r\n"
                         : "=A"(ret)
                         : "b"(addr)
                         );
    return ret;
}

static inline void write_config_reg(uint32_t config_regs_base, uint32_t reg,
                                    uint64_t val)
{
    /* these are MMIO so make sure compiler doesn't optimize */
    //*(volatile uint64_t *)(unsigned long)(config_regs_base + reg) =
    //val;
    u32 addr = config_regs_base + reg;

    __asm__ __volatile__("movl %%eax, %%fs:(%%ebx)\r\n"
                         "movl %%edx, %%fs:4(%%ebx)\r\n"
                         :
                         : "A"(val), "b"(addr)
                         );

}



/***********************************************************
 These next two taken from tboot-20101005/tboot/include/txt/
 **********************************************************/

/*
 * for SW errors (ERRORCODE.external = 1)
 */
typedef union {
    uint32_t _raw;
    struct {
        uint32_t  err1    : 15;     /* specific to src */
        uint32_t  src     : 1;      /* 0=ACM, 1=other */
        uint32_t  err2    : 14;     /* specific to src */
    };
} txt_errorcode_sw_t;

/*
 * ACM errors (txt_errorcode_sw_t.src=0), format of err field
 */
typedef union {
    uint32_t _raw;
    struct {
        uint32_t acm_type  : 4;  /* 0000=BIOS ACM, 0001=SINIT, */
                                 /* 0010-1111=reserved */
        uint32_t progress  : 6;
        uint32_t error     : 4;
        uint32_t reserved  : 1;
        uint32_t src       : 1;  /* above value */
        uint32_t error2    : 14; /* sub-error */
    };
} acmod_error_t;













//#include "_txt_mle.h"
/*
 * SINIT/MLE capabilities
 */
typedef union {
    uint32_t  _raw;
    struct {
        uint32_t  rlp_wake_getsec     : 1;
        uint32_t  rlp_wake_monitor    : 1;
        uint32_t  ecx_pgtbl           : 1;
        uint32_t  reserved            : 29;
    };
} txt_caps_t;


/* taken from tboot-20101005/include/uuid.h */
typedef struct __packed {
  uint32_t    data1;
  uint16_t    data2;
  uint16_t    data3;
  uint16_t    data4;
  uint8_t     data5[6];
} uuid_t;

/* static inline bool are_uuids_equal(const uuid_t *uuid1, const uuid_t *uuid2) */
/* { */
/*     return (memcmp(uuid1, uuid2, sizeof(*uuid1)) == 0); */
/* } */

/*
 * MLE header structure
 *   describes an MLE for SINIT and OS/loader SW
 */
typedef struct {
    uuid_t      uuid;
    uint32_t    length;
    uint32_t    version;
    uint32_t    entry_point;
    uint32_t    first_valid_page;
    uint32_t    mle_start_off;
    uint32_t    mle_end_off;
    txt_caps_t  capabilities;
    uint32_t    cmdline_start_off;
    uint32_t    cmdline_end_off;
} mle_hdr_t;

#define MLE_HDR_UUID      {0x9082ac5a, 0x476f, 0x74a7, 0x5c0f, \
                              {0x55, 0xa2, 0xcb, 0x51, 0xb6, 0x42}}

/*
 * values supported by current version of tboot
 */
#define MLE_HDR_VER       0x00020001     /* 2.1 */
#define MLE_HDR_CAPS      0x00000007     /* rlp_wake_{getsec, monitor} = 1,
                                            ecx_pgtbl = 1 */

/* from tboot-20101005/include/tb_error.h */
typedef enum {
    TB_ERR_NONE                = 0,         /* succeed */
    TB_ERR_FIXED               = 1,         /* previous error has been fixed */

    TB_ERR_GENERIC,                         /* non-fatal generic error */

    TB_ERR_TPM_NOT_READY,                   /* tpm not ready */
    TB_ERR_SMX_NOT_SUPPORTED,               /* smx not supported */
    TB_ERR_VMX_NOT_SUPPORTED,               /* vmx not supported */
    TB_ERR_TXT_NOT_SUPPORTED,               /* txt not supported */

    TB_ERR_MODULE_VERIFICATION_FAILED,      /* module failed to verify against
                                               policy */
    TB_ERR_MODULES_NOT_IN_POLICY,           /* modules in mbi but not in
                                               policy */
    TB_ERR_POLICY_INVALID,                  /* policy is invalid */
    TB_ERR_POLICY_NOT_PRESENT,              /* no policy in TPM NV */

    TB_ERR_SINIT_NOT_PRESENT,               /* SINIT ACM not provided */
    TB_ERR_ACMOD_VERIFY_FAILED,             /* verifying AC module failed */

    TB_ERR_POST_LAUNCH_VERIFICATION,        /* verification of post-launch
                                               failed */
    TB_ERR_S3_INTEGRITY,                    /* creation or verification of
                                               S3 integrity measurements
                                               failed */

    TB_ERR_FATAL,                           /* generic fatal error */
    TB_ERR_MAX
} tb_error_t;












//#include "_txt_smx.h"
/*
 * GETSEC[] instructions
 */

/* GETSEC instruction opcode */
#define IA32_GETSEC_OPCODE		".byte 0x0f,0x37"

/* GETSEC leaf function codes */
#define IA32_GETSEC_CAPABILITIES	0
#define IA32_GETSEC_SENTER		4
#define IA32_GETSEC_SEXIT		5
#define IA32_GETSEC_PARAMETERS		6
#define IA32_GETSEC_SMCTRL		7
#define IA32_GETSEC_WAKEUP		8

/*
 * GETSEC[] leaf functions
 */

typedef union {
    uint32_t _raw;
    struct {
        uint32_t chipset_present  : 1;
        uint32_t undefined1	  : 1;
        uint32_t enteraccs	  : 1;
        uint32_t exitac	          : 1;
        uint32_t senter	          : 1;
        uint32_t sexit	          : 1;
        uint32_t parameters	  : 1;
        uint32_t smctrl	          : 1;
        uint32_t wakeup	          : 1;
        uint32_t undefined9	  : 22;
        uint32_t extended_leafs   : 1;
    };
} capabilities_t;

static inline uint32_t __getsec_capabilities(uint32_t index)
{
    uint32_t cap;
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
              : "=a"(cap)
              : "a"(IA32_GETSEC_CAPABILITIES), "b"(index));
    return cap;
}

/* helper fn. for getsec_capabilities */
/* this is arbitrary and can be increased when needed */
#define MAX_SUPPORTED_ACM_VERSIONS      16

typedef struct {
    struct {
        uint32_t mask;
        uint32_t version;
    } acm_versions[MAX_SUPPORTED_ACM_VERSIONS];
    int n_versions;
    uint32_t acm_max_size;
    uint32_t acm_mem_types;
    uint32_t senter_controls;
    bool proc_based_scrtm;
    bool preserve_mce;
} getsec_parameters_t;

///extern bool get_parameters(getsec_parameters_t *params);


static inline void __getsec_senter(uint32_t sinit_base, uint32_t sinit_size)
{
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
			  :
			  : "a"(IA32_GETSEC_SENTER),
			    "b"(sinit_base),
			    "c"(sinit_size),
			    "d"(0x0));
}

static inline void __getsec_sexit(void)
{
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
                          : : "a"(IA32_GETSEC_SEXIT));
}

static inline void __getsec_wakeup(void)
{
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
                          : : "a"(IA32_GETSEC_WAKEUP));
}

static inline void __getsec_smctrl(void)
{
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
                          : : "a"(IA32_GETSEC_SMCTRL), "b"(0x0));
}

static inline void __getsec_parameters(uint32_t index, int* param_type,
                                       uint32_t* peax, uint32_t* pebx,
                                       uint32_t* pecx)
{
    uint32_t eax=0, ebx=0, ecx=0;
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
                          : "=a"(eax), "=b"(ebx), "=c"(ecx)
                          : "a"(IA32_GETSEC_PARAMETERS), "b"(index));

    if ( param_type != NULL )   *param_type = eax & 0x1f;
    if ( peax != NULL )         *peax = eax;
    if ( pebx != NULL )         *pebx = ebx;
    if ( pecx != NULL )         *pecx = ecx;
}


bool txt_prepare_cpu(void);
tb_error_t txt_launch_environment(void *sinit_ptr, size_t sinit_size,
                                  void *phys_mle_start, size_t mle_size);












//#include "_txt_mtrrs.h"
#define MTRR_TYPE_MIXED         -1
#define MMIO_APIC_BASE          0xFEE00000
#define NR_MMIO_APIC_PAGES      1
#define NR_MMIO_IOAPIC_PAGES    1
#define NR_MMIO_PCICFG_PAGES    1











//#include "_txt_heap.h"
/*
 * data-passing structures contained in TXT heap:
 *   - BIOS
 *   - OS/loader to MLE
 *   - OS/loader to SINIT
 *   - SINIT to MLE
 */

/*
 * BIOS structure
 */
typedef struct {
    uint32_t  version;              /* WB = 2, current = 3 */
    uint32_t  bios_sinit_size;
    uint64_t  lcp_pd_base;
    uint64_t  lcp_pd_size;
    uint32_t  num_logical_procs;
    /* versions >= 3 */
    uint64_t  flags;
} __attribute__ ((packed)) bios_data_t;

/*
 * OS/loader to MLE structure
 *   - private to tboot (so can be any format we need)
 */
#define MAX_LCP_PO_DATA_SIZE     64*1024  /* 64k */

typedef struct {
    uint32_t          version;           /* currently 2 */
    mtrr_state_t      saved_mtrr_state;  /* saved prior to changes for SINIT */
    //multiboot_info_t* mbi;               /* needs to be restored to ebx */
    void *mbi;
    uint32_t          saved_misc_enable_msr;  /* saved prior to SENTER */
                                         /* PO policy data */
    uint8_t           lcp_po_data[MAX_LCP_PO_DATA_SIZE];
} __attribute__ ((packed)) os_mle_data_t;

/*
 * OS/loader to SINIT structure
 */
typedef struct {
    uint32_t    version;           /* currently 4, 5 */
    uint32_t    reserved;
    uint64_t    mle_ptab;
    uint64_t    mle_size;
    uint64_t    mle_hdr_base;
    uint64_t    vtd_pmr_lo_base;
    uint64_t    vtd_pmr_lo_size;
    uint64_t    vtd_pmr_hi_base;
    uint64_t    vtd_pmr_hi_size;
    uint64_t    lcp_po_base;
    uint64_t    lcp_po_size;
    txt_caps_t  capabilities;
    /* versions >= 5 */
    uint64_t    efi_rsdt_ptr;
} __attribute__ ((packed)) os_sinit_data_t;

/*
 * SINIT to MLE structure
 */
#define MDR_MEMTYPE_GOOD                0x00
#define MDR_MEMTYPE_SMM_OVERLAY         0x01
#define MDR_MEMTYPE_SMM_NONOVERLAY      0x02
#define MDR_MEMTYPE_PCIE_CONFIG_SPACE   0x03
#define MDR_MEMTYPE_PROTECTED           0x04

typedef struct __attribute__ ((packed)) {
    uint64_t  base;
    uint64_t  length;
    uint8_t   mem_type;
    uint8_t   reserved[7];
} __attribute__ ((packed)) sinit_mdr_t;

#define SHA1_SIZE      20
typedef uint8_t   sha1_hash_t[SHA1_SIZE];

typedef struct {
    uint32_t     version;             /* currently 6-8 */
    sha1_hash_t  bios_acm_id;
    uint32_t     edx_senter_flags;
    uint64_t     mseg_valid;
    sha1_hash_t  sinit_hash;
    sha1_hash_t  mle_hash;
    sha1_hash_t  stm_hash;
    sha1_hash_t  lcp_policy_hash;
    uint32_t     lcp_policy_control;
    uint32_t     rlp_wakeup_addr;
    uint32_t     reserved;
    uint32_t     num_mdrs;
    uint32_t     mdrs_off;
    uint32_t     num_vtd_dmars;
    uint32_t     vtd_dmars_off;
    /* versions >= 8 */
    uint32_t     proc_scrtm_status;
} __attribute__ ((packed)) sinit_mle_data_t;



extern bool verify_txt_heap(txt_heap_t *txt_heap, bool bios_data_only);
extern bool verify_bios_data(txt_heap_t *txt_heap);
extern void print_os_sinit_data(os_sinit_data_t *os_sinit_data);



#endif //__ASSEMBLY__

#endif /* __UNI_TXT_ */
