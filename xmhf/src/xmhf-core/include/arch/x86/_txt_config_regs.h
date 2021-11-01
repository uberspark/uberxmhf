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
 * config_regs.h: Intel(r) TXT configuration register -related definitions
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

#ifndef __TXT_CONFIG_REGS_H__
#define __TXT_CONFIG_REGS_H__

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

static inline uint64_t read_pub_config_reg(uint32_t reg)
{
    return read_config_reg(TXT_PUB_CONFIG_REGS_BASE, reg);
}

static inline void write_pub_config_reg(uint32_t reg, uint64_t val)
{
    write_config_reg(TXT_PUB_CONFIG_REGS_BASE, reg, val);
}

static inline uint64_t read_priv_config_reg(uint32_t reg)
{
    return read_config_reg(TXT_PRIV_CONFIG_REGS_BASE, reg);
}

static inline void write_priv_config_reg(uint32_t reg, uint64_t val)
{
    write_config_reg(TXT_PRIV_CONFIG_REGS_BASE, reg, val);
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






#endif /* __TXT_CONFIG_REGS_H__ */

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
