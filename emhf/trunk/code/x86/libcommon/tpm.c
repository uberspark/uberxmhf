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

/*
 * tpm.c: TPM-related support functions
 *
 * Copyright (c) 2006-2010, Intel Corporation
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
 * Modified for EMHF by jonmccune@cmu.edu, 2011.01.18
 */

#include <target.h>
#include <sha1.h>
#include <tpm.h>


/* TODO: Give these a more appropriate home */
/* #define readb(va)       (*(volatile uint8_t *) (va)) */
/* #define writeb(va, d)   (*(volatile uint8_t *) (va) = (d)) */

static inline void writeb(u32 addr, u8 val) {
    __asm__ __volatile__("movb %%al, %%fs:(%%ebx)\r\n"
                         :
                         : "b"(addr), "a"((u32)val)
                         );
}

static inline u8 readb(u32 addr) {
    u32 ret;
    __asm__ __volatile("xor %%eax, %%eax\r\n"        
                       "movb %%fs:(%%ebx), %%al\r\n"
                       : "=a"(ret)
                       : "b"(addr)
                       );
    return (u8)ret;        
}

/* un-comment to enable detailed command tracing */
#define TPM_TRACE

/* ~5 secs are required for Infineon that requires this, so leave some extra */
#define MAX_SAVESTATE_RETRIES       60

#define TPM_TAG_RQU_COMMAND         0x00C1
#define TPM_TAG_RQU_AUTH1_COMMAND   0x00C2
#define TPM_TAG_RQU_AUTH2_COMMAND   0x00C3
#define TPM_ORD_PCR_EXTEND          0x00000014
#define TPM_ORD_PCR_READ            0x00000015
#define TPM_ORD_PCR_RESET           0x000000C8
#define TPM_ORD_NV_READ_VALUE       0x000000CF
#define TPM_ORD_NV_WRITE_VALUE      0x000000CD
#define TPM_ORD_GET_CAPABILITY      0x00000065
#define TPM_ORD_SEAL                0x00000017
#define TPM_ORD_UNSEAL              0x00000018
#define TPM_ORD_OSAP                0x0000000B
#define TPM_ORD_OIAP                0x0000000A
#define TPM_ORD_SAVE_STATE          0x00000098
#define TPM_ORD_GET_RANDOM          0x00000046

#define TPM_TAG_PCR_INFO_LONG       0x0006
#define TPM_TAG_STORED_DATA12       0x0016

/*
 * TPM registers and data structures
 *
 * register values are offsets from each locality base
 * see {read,write}_tpm_reg() for data struct format
 */

/* TPM_ACCESS_x */
#define TPM_REG_ACCESS           0x00
typedef union {
    u8 _raw[1];                      /* 1-byte reg */
    struct __attribute__ ((packed)) {
        u8 tpm_establishment   : 1;  /* RO, 0=T/OS has been established
                                        before */
        u8 request_use         : 1;  /* RW, 1=locality is requesting TPM use */
        u8 pending_request     : 1;  /* RO, 1=other locality is requesting
                                        TPM usage */
        u8 seize               : 1;  /* WO, 1=seize locality */
        u8 been_seized         : 1;  /* RW, 1=locality seized while active */
        u8 active_locality     : 1;  /* RW, 1=locality is active */
        u8 reserved            : 1;
        u8 tpm_reg_valid_sts   : 1;  /* RO, 1=other bits are valid */
    };
} tpm_reg_access_t;

/* TPM_STS_x */
#define TPM_REG_STS              0x18
typedef union {
    u8 _raw[3];                  /* 3-byte reg */
    struct __attribute__ ((packed)) {
        u8 reserved1       : 1;
        u8 response_retry  : 1;  /* WO, 1=re-send response */
        u8 reserved2       : 1;
        u8 expect          : 1;  /* RO, 1=more data for command expected */
        u8 data_avail      : 1;  /* RO, 0=no more data for response */
        u8 tpm_go          : 1;  /* WO, 1=execute sent command */
        u8 command_ready   : 1;  /* RW, 1=TPM ready to receive new cmd */
        u8 sts_valid       : 1;  /* RO, 1=data_avail and expect bits are
                                    valid */
        u16 burst_count    : 16; /* RO, # read/writes bytes before wait */
    };
} tpm_reg_sts_t;

/* TPM_DATA_FIFO_x */
#define TPM_REG_DATA_FIFO        0x24
typedef union {
        uint8_t _raw[1];                      /* 1-byte reg */
} tpm_reg_data_fifo_t;

/*
 * assumes that all reg types follow above format:
 *   - packed
 *   - member named '_raw' which is array whose size is that of data to read
 */
#define read_tpm_reg(locality, reg, pdata)      \
    _read_tpm_reg(locality, reg, (pdata)->_raw, sizeof(*(pdata)))

#define write_tpm_reg(locality, reg, pdata)     \
    _write_tpm_reg(locality, reg, (pdata)->_raw, sizeof(*(pdata)))


static void _read_tpm_reg(int locality, u32 reg, u8 *_raw, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ )
        _raw[i] = readb((TPM_LOCALITY_BASE_N(locality) | reg) + i);
}

static void _write_tpm_reg(int locality, u32 reg, u8 *_raw, size_t size)
{
    size_t i;    
    for ( i = 0; i < size; i++ )
        writeb((TPM_LOCALITY_BASE_N(locality) | reg) + i, _raw[i]);
}

/*
 * the following inline function reversely copy the bytes from 'in' to
 * 'out', the byte number to copy is given in count.
 */
#define reverse_copy(out, in, count) \
    _reverse_copy((uint8_t *)(out), (const uint8_t *)(in), count)

static inline void _reverse_copy(uint8_t *out, const uint8_t *in, uint32_t count)
{
    uint32_t i;    
    for ( i = 0; i < count; i++ )
        out[i] = in[count - i - 1];
}

#define TPM_VALIDATE_LOCALITY_TIME_OUT  0x100

static bool tpm_validate_locality(uint32_t locality)
{
    uint32_t i;
    tpm_reg_access_t reg_acc;

    for ( i = TPM_VALIDATE_LOCALITY_TIME_OUT; i > 0; i-- ) {
        /*
         * TCG spec defines reg_acc.tpm_reg_valid_sts bit to indicate whether
         * other bits of access reg are valid.( but this bit will also be 1
         * while this locality is not available, so check seize bit too)
         * It also defines that reading reg_acc.seize should always return 0
         */
        read_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
        if ( reg_acc.tpm_reg_valid_sts == 1 && reg_acc.seize == 0)
            return true;
        cpu_relax();
    }

    if ( i <= 0 )
        printf("\nTPM: tpm_validate_locality timeout\n");

    return false;
}

#define TIMEOUT_UNIT    (0x100000 / 330) /* ~1ms, 1 tpm r/w need > 330ns */
#define TIMEOUT_A       750  /* 750ms */
#define TIMEOUT_B       2000 /* 2s */
#define TIMEOUT_C       750  /* 750ms */
#define TIMEOUT_D       750  /* 750ms */

typedef struct __attribute__ ((packed)) {
    uint32_t timeout_a;
    uint32_t timeout_b;
    uint32_t timeout_c;
    uint32_t timeout_d;
} tpm_timeout_t;

static tpm_timeout_t g_timeout = {TIMEOUT_A,
                                  TIMEOUT_B,
                                  TIMEOUT_C,
                                  TIMEOUT_D};

#define TPM_ACTIVE_LOCALITY_TIME_OUT    \
          (TIMEOUT_UNIT * g_timeout.timeout_a)  /* according to spec */
#define TPM_CMD_READY_TIME_OUT          \
          (TIMEOUT_UNIT * g_timeout.timeout_b)  /* according to spec */
#define TPM_CMD_WRITE_TIME_OUT          \
          (TIMEOUT_UNIT * g_timeout.timeout_d)  /* let it long enough */
#define TPM_DATA_AVAIL_TIME_OUT         \
          (TIMEOUT_UNIT * g_timeout.timeout_c)  /* let it long enough */
#define TPM_RSP_READ_TIME_OUT           \
          (TIMEOUT_UNIT * g_timeout.timeout_d)  /* let it long enough */

static uint32_t tpm_wait_cmd_ready(uint32_t locality)
{
    uint32_t            i;
    tpm_reg_access_t    reg_acc;
    tpm_reg_sts_t       reg_sts;

    /* ensure the contents of the ACCESS register are valid */
    read_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
#ifdef TPM_TRACE
    printf("TPM: Access reg content: 0x%02x\n", (uint32_t)reg_acc._raw[0]);
#endif
    if ( reg_acc.tpm_reg_valid_sts == 0 ) {
        printf("TPM: Access reg not valid\n");
        return TPM_FAIL;
    }

    /* request access to the TPM from locality N */
    reg_acc._raw[0] = 0;
    reg_acc.request_use = 1;
    write_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);

    i = 0;
    do {
        read_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
        if ( reg_acc.active_locality == 1 )
            break;
        else
            cpu_relax();
        i++;
    } while ( i <= TPM_ACTIVE_LOCALITY_TIME_OUT);

    if ( i > TPM_ACTIVE_LOCALITY_TIME_OUT ) {
        printf("TPM: access reg request use timeout\n");
        return TPM_FAIL;
    }

    /* ensure the TPM is ready to accept a command */
#ifdef TPM_TRACE
    printf("TPM: wait for cmd ready ");
#endif
    i = 0;
    do {
        /* write 1 to TPM_STS_x.commandReady to let TPM enter ready state */
        memset((void *)&reg_sts, 0, sizeof(reg_sts));
        reg_sts.command_ready = 1;
        write_tpm_reg(locality, TPM_REG_STS, &reg_sts);
        cpu_relax();

        /* then see if it has */
        read_tpm_reg(locality, TPM_REG_STS, &reg_sts);
#ifdef TPM_TRACE
        printf(".");
#endif
        if ( reg_sts.command_ready == 1 )
            break;
        else
            cpu_relax();
        i++;
    } while ( i <= TPM_CMD_READY_TIME_OUT );
#ifdef TPM_TRACE
    printf("\n");
#endif

    if ( i > TPM_CMD_READY_TIME_OUT ) {
        printf("TPM: status reg content: %02x %02x %02x\n",
               (uint32_t)reg_sts._raw[0],
               (uint32_t)reg_sts._raw[1],
               (uint32_t)reg_sts._raw[2]);
        printf("TPM: tpm timeout for command_ready\n");
        goto RelinquishControl;
    }
    return TPM_SUCCESS;

RelinquishControl:
    /* deactivate current locality */
    reg_acc._raw[0] = 0;
    reg_acc.active_locality = 1;
    write_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);

    return TPM_FAIL;
}

/*
 *   locality : TPM locality (0 - 3)
 *   in       : All bytes for a single TPM command, including TAG, SIZE,
 *              ORDINAL, and other arguments. All data should be in big-endian
 *              style. The in MUST NOT be NULL, containing at least 10 bytes.
 *              0   1   2   3   4   5   6   7   8   9   10  ...
 *              -------------------------------------------------------------
 *              | TAG  |     SIZE      |    ORDINAL    |    arguments ...
 *              -------------------------------------------------------------
 *   in_size  : The size of the whole command contained within the in buffer.
 *              It should equal to the SIZE contained in the in buffer.
 *   out      : All bytes of the TPM response to a single command. All data
 *              within it will be in big-endian style. The out MUST not be
 *              NULL, and will return at least 10 bytes.
 *              0   1   2   3   4   5   6   7   8   9   10  ...
 *              -------------------------------------------------------------
 *              | TAG  |     SIZE      |  RETURN CODE  |    other data ...
 *              -------------------------------------------------------------
 *   out_size : In/out paramter. As in, it is the size of the out buffer;
 *              as out, it is the size of the response within the out buffer.
 *              The out_size MUST NOT be NULL.
 *   return   : 0 = success; if not 0, it equal to the RETURN CODE in out buf.
 */
#define CMD_HEAD_SIZE           10
#define RSP_HEAD_SIZE           10
#define CMD_SIZE_OFFSET         2
#define CMD_ORD_OFFSET          6
#define RSP_SIZE_OFFSET         2
#define RSP_RST_OFFSET          6

static uint32_t tpm_write_cmd_fifo(uint32_t locality, uint8_t *in,
                                   uint32_t in_size, uint8_t *out,
                                   uint32_t *out_size)
{
    uint32_t            i, rsp_size, offset, ret;
    uint16_t            row_size;
    tpm_reg_access_t    reg_acc;
    tpm_reg_sts_t       reg_sts;

    if ( locality >= TPM_NR_LOCALITIES ) {
        printf("TPM: Invalid locality for tpm_write_cmd_fifo()\n");
        return TPM_BAD_PARAMETER;
    }
    if ( in == NULL || out == NULL || out_size == NULL ) {
        printf("TPM: Invalid parameter for tpm_write_cmd_fifo()\n");
        return TPM_BAD_PARAMETER;
    }
    if ( in_size < CMD_HEAD_SIZE || *out_size < RSP_HEAD_SIZE ) {
        printf("TPM: in/out buf size must be larger than 10 bytes\n");
        return TPM_BAD_PARAMETER;
    }

    if ( !tpm_validate_locality(locality) ) {
        printf("TPM: Locality %d is not open\n", locality);
        return TPM_FAIL;
    }

    ret = tpm_wait_cmd_ready(locality);
    if ( ret != TPM_SUCCESS )
        return ret;

#ifdef TPM_TRACE
    {
        printf("TPM: cmd size = %d\nTPM: cmd content: ", in_size);
        print_hex("TPM: \t", in, in_size);
    }
#endif

    /* write the command to the TPM FIFO */
    offset = 0;
    do {
        i = 0;
        do {
            read_tpm_reg(locality, TPM_REG_STS, &reg_sts);
            /* find out how many bytes the TPM can accept in a row */
            row_size = reg_sts.burst_count;
            if ( row_size > 0 )
                break;
            else
                cpu_relax();
            i++;
        } while ( i <= TPM_CMD_WRITE_TIME_OUT );
        if ( i > TPM_CMD_WRITE_TIME_OUT ) {
            printf("TPM: write cmd timeout\n");
            ret = TPM_FAIL;
            goto RelinquishControl;
        }

        for ( ; row_size > 0 && offset < in_size; row_size--, offset++ )
            write_tpm_reg(locality, TPM_REG_DATA_FIFO,
                          (tpm_reg_data_fifo_t *)&in[offset]);
    } while ( offset < in_size );

    /* command has been written to the TPM, it is time to execute it. */
    memset(&reg_sts, 0,  sizeof(reg_sts));
    reg_sts.tpm_go = 1;
    write_tpm_reg(locality, TPM_REG_STS, &reg_sts);

    /* check for data available */
    i = 0;
    do {
        read_tpm_reg(locality,TPM_REG_STS, &reg_sts);
        if ( reg_sts.sts_valid == 1 && reg_sts.data_avail == 1 )
            break;
        else
            cpu_relax();
        i++;
    } while ( i <= TPM_DATA_AVAIL_TIME_OUT );
    if ( i > TPM_DATA_AVAIL_TIME_OUT ) {
        printf("TPM: wait for data available timeout\n");
        ret = TPM_FAIL;
        goto RelinquishControl;
    }

    rsp_size = 0;
    offset = 0;
    do {
        /* find out how many bytes the TPM returned in a row */
        i = 0;
        do {
            read_tpm_reg(locality, TPM_REG_STS, &reg_sts);
            row_size = reg_sts.burst_count;
            if ( row_size > 0 )
                break;
            else
                cpu_relax();
            i++;
        } while ( i <= TPM_RSP_READ_TIME_OUT );
        if ( i > TPM_RSP_READ_TIME_OUT ) {
            printf("TPM: read rsp timeout\n");
            ret = TPM_FAIL;
            goto RelinquishControl;
        }

        for ( ; row_size > 0 && offset < *out_size; row_size--, offset++ ) {
            if ( offset < *out_size )
                read_tpm_reg(locality, TPM_REG_DATA_FIFO,
                             (tpm_reg_data_fifo_t *)&out[offset]);
            else {
                /* discard the responded bytes exceeding out buf size */
                tpm_reg_data_fifo_t discard;
                read_tpm_reg(locality, TPM_REG_DATA_FIFO,
                             (tpm_reg_data_fifo_t *)&discard);
            }

            /* get outgoing data size */
            if ( offset == RSP_RST_OFFSET - 1 ) {
                reverse_copy(&rsp_size, &out[RSP_SIZE_OFFSET],
                             sizeof(rsp_size));
            }
        }
    } while ( offset < RSP_RST_OFFSET ||
              (offset < rsp_size && offset < *out_size) );

    *out_size = (*out_size > rsp_size) ? rsp_size : *out_size;

    /* out buffer contains the complete outgoing data, get return code */
    reverse_copy(&ret, &out[RSP_RST_OFFSET], sizeof(ret));

#ifdef TPM_TRACE
    {
        printf("TPM: response size = %d\n", *out_size);
        printf("TPM: response content: ");
        print_hex("TPM: \t", out, *out_size);
    }
#endif

    memset(&reg_sts, 0, sizeof(reg_sts));
    reg_sts.command_ready = 1;
    write_tpm_reg(locality, TPM_REG_STS, &reg_sts);

RelinquishControl:
    /* deactivate current locality */
    reg_acc._raw[0] = 0;
    reg_acc.active_locality = 1;
    write_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);

    return ret;
}

/*
 * The _tpm_submit_cmd function comes with 2 global buffers: cmd_buf & rsp_buf.
 * Before calling, caller should fill cmd arguements into cmd_buf via
 * WRAPPER_IN_BUF macro. After calling, caller should fetch result from
 * rsp_buffer via WRAPPER_OUT_BUF macro.
 * cmd_buf content:
 *  0   1   2   3   4   5   6   7   8   9   10  ...
 * -------------------------------------------------------------
 * |  TAG  |     SIZE      |    ORDINAL    |    arguments ...
 * -------------------------------------------------------------
 * rsp_buf content:
 *  0   1   2   3   4   5   6   7   8   9   10  ...
 * -------------------------------------------------------------
 * |  TAG  |     SIZE      |  RETURN CODE  |    other data ...
 * -------------------------------------------------------------
 *
 *   locality : TPM locality (0 - 4)
 *   tag      : The TPM command tag
 *   cmd      : The TPM command ordinal
 *   arg_size : Size of argument data.
 *   out_size : IN/OUT paramter. The IN is the expected size of out data;
 *              the OUT is the size of output data within out buffer.
 *              The out_size MUST NOT be NULL.
 *   return   : TPM_SUCCESS for success, for other error code, refer to the .h
 */
static uint8_t     cmd_buf[TPM_CMD_SIZE_MAX];
static uint8_t     rsp_buf[TPM_RSP_SIZE_MAX];
#define WRAPPER_IN_BUF          (cmd_buf + CMD_HEAD_SIZE)
#define WRAPPER_OUT_BUF         (rsp_buf + RSP_HEAD_SIZE)
#define WRAPPER_IN_MAX_SIZE     (TPM_CMD_SIZE_MAX - CMD_HEAD_SIZE)
#define WRAPPER_OUT_MAX_SIZE    (TPM_RSP_SIZE_MAX - RSP_HEAD_SIZE)

static uint32_t _tpm_submit_cmd(uint32_t locality, uint16_t tag, uint32_t cmd,
                               uint32_t arg_size, uint32_t *out_size)
{
    uint32_t    ret;
    uint32_t    cmd_size, rsp_size = 0;

    if ( out_size == NULL ) {
        printf("TPM: invalid param for _tpm_submit_cmd()\n");
        return TPM_BAD_PARAMETER;
    }

    /*
     * real cmd size should add 10 more bytes:
     *      2 bytes for tag
     *      4 bytes for size
     *      4 bytes for ordinal
     */
    cmd_size = CMD_HEAD_SIZE + arg_size;

    if ( cmd_size > TPM_CMD_SIZE_MAX ) {
        printf("TPM: cmd exceeds the max supported size.\n");
        return TPM_BAD_PARAMETER;
    }

    /* copy tag, size & ordinal into buf in a reversed byte order */
    reverse_copy(cmd_buf, &tag, sizeof(tag));
    reverse_copy(cmd_buf + CMD_SIZE_OFFSET, &cmd_size, sizeof(cmd_size));
    reverse_copy(cmd_buf + CMD_ORD_OFFSET, &cmd, sizeof(cmd));

    rsp_size = RSP_HEAD_SIZE + *out_size;
    rsp_size = (rsp_size > TPM_RSP_SIZE_MAX) ? TPM_RSP_SIZE_MAX: rsp_size;
    ret = tpm_write_cmd_fifo(locality, cmd_buf, cmd_size, rsp_buf, &rsp_size);

    /*
     * should subtract 10 bytes from real response size:
     *      2 bytes for tag
     *      4 bytes for size
     *      4 bytes for return code
     */
    rsp_size -= (rsp_size > RSP_HEAD_SIZE) ? RSP_HEAD_SIZE : rsp_size;

    if ( ret != TPM_SUCCESS )
        return ret;

    if ( *out_size == 0 || rsp_size == 0 )
        *out_size = 0;
    else
        *out_size = (rsp_size < *out_size) ? rsp_size : *out_size;

    return ret;
}

static inline uint32_t tpm_submit_cmd(uint32_t locality, uint32_t cmd,
                                      uint32_t arg_size, uint32_t *out_size)
{
   return  _tpm_submit_cmd(locality, TPM_TAG_RQU_COMMAND, cmd,
                           arg_size, out_size);
}

static inline uint32_t tpm_submit_cmd_auth1(uint32_t locality, uint32_t cmd,
                                      uint32_t arg_size, uint32_t *out_size)
{
   return  _tpm_submit_cmd(locality, TPM_TAG_RQU_AUTH1_COMMAND, cmd,
                           arg_size, out_size);
}

static inline uint32_t tpm_submit_cmd_auth2(uint32_t locality, uint32_t cmd,
                                      uint32_t arg_size, uint32_t *out_size)
{
   return  _tpm_submit_cmd(locality, TPM_TAG_RQU_AUTH2_COMMAND, cmd,
                           arg_size, out_size);
}

uint32_t tpm_pcr_read(uint32_t locality, uint32_t pcr, tpm_pcr_value_t *out)
{
    uint32_t ret, out_size = sizeof(*out);

    if ( out == NULL )
        return TPM_BAD_PARAMETER;
    if ( pcr >= TPM_NR_PCRS )
        return TPM_BAD_PARAMETER;

    /* copy pcr into buf in reversed byte order */
    reverse_copy(WRAPPER_IN_BUF, &pcr, sizeof(pcr));

    ret = tpm_submit_cmd(locality, TPM_ORD_PCR_READ, sizeof(pcr), &out_size);

#ifdef TPM_TRACE
    printf("TPM: Pcr %d Read return value = %08X\n", pcr, ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: Pcr %d Read return value = %08X\n", pcr, ret);
        return ret;
    }

    if ( out_size > sizeof(*out) )
        out_size = sizeof(*out);
    memcpy((void *)out, WRAPPER_OUT_BUF, out_size);

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, out->digest, out_size);
    }
#endif

    return ret;
}

uint32_t tpm_pcr_extend(uint32_t locality, uint32_t pcr,
                        const tpm_digest_t* in, tpm_pcr_value_t* out)
{
    uint32_t ret, in_size = 0, out_size;

    if ( in == NULL )
        return TPM_BAD_PARAMETER;
    if ( pcr >= TPM_NR_PCRS )
        return TPM_BAD_PARAMETER;
    if ( out == NULL )
        out_size = 0;
    else
        out_size = sizeof(*out);

    /* copy pcr into buf in reversed byte order, then copy in data */
    reverse_copy(WRAPPER_IN_BUF, &pcr, sizeof(pcr));
    in_size += sizeof(pcr);
    memcpy(WRAPPER_IN_BUF + in_size, (const void *)in, sizeof(*in));
    in_size += sizeof(*in);

    ret = tpm_submit_cmd(locality, TPM_ORD_PCR_EXTEND, in_size, &out_size);

#ifdef TPM_TRACE
    printf("TPM: Pcr %d extend, return value = %08X\n", pcr, ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: Pcr %d extend, return value = %08X\n", pcr, ret);
        return ret;
    }

    if ( out != NULL && out_size > 0 ) {
       out_size = (out_size > sizeof(*out)) ? sizeof(*out) : out_size;
       memcpy((void *)out, WRAPPER_OUT_BUF, out_size);
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, out->digest, out_size);
    }
#endif

    return ret;
}

typedef struct __attribute__ ((packed)) {
    uint16_t    size_of_select;
    uint8_t     pcr_select[3];
} tpm_pcr_selection_t;

uint32_t tpm_pcr_reset(uint32_t locality, uint32_t pcr)
{
    uint32_t ret, in_size, out_size = 0;
    uint16_t size_of_select;
    tpm_pcr_selection_t pcr_sel = {0,{0,}};

    if ( pcr >= TPM_NR_PCRS || pcr < TPM_PCR_RESETABLE_MIN )
        return TPM_BAD_PARAMETER;

    /* the pcr_sel.pcr_select[size_of_select - 1] should not be 0 */
    size_of_select = pcr / 8 + 1;
    reverse_copy(&pcr_sel.size_of_select, &size_of_select,
                 sizeof(size_of_select));
    pcr_sel.pcr_select[pcr / 8] = 1 << (pcr % 8);

    in_size = sizeof(pcr_sel);
    memcpy(WRAPPER_IN_BUF, (void *)&pcr_sel, in_size);

    ret = tpm_submit_cmd(locality, TPM_ORD_PCR_RESET, in_size, &out_size);

    printf("TPM: Pcr %d reset, return value = %08X\n", pcr, ret);

    return ret;
}

uint32_t tpm_nv_read_value(uint32_t locality, tpm_nv_index_t index,
                           uint32_t offset, uint8_t *data,
                           uint32_t *data_size)
{
    uint32_t ret, in_size = 0, out_size;

    if ( data == NULL || data_size == NULL )
        return TPM_BAD_PARAMETER;
    if ( *data_size == 0 )
        return TPM_BAD_PARAMETER;
    if ( *data_size > TPM_NV_READ_VALUE_DATA_SIZE_MAX )
        *data_size = TPM_NV_READ_VALUE_DATA_SIZE_MAX;

    /* copy the index, offset and *data_size into buf in reversed byte order */
    reverse_copy(WRAPPER_IN_BUF, &index, sizeof(index));
    in_size += sizeof(index);
    reverse_copy(WRAPPER_IN_BUF + in_size, &offset, sizeof(offset));
    in_size += sizeof(offset);
    reverse_copy(WRAPPER_IN_BUF + in_size, data_size, sizeof(*data_size));
    in_size += sizeof(*data_size);

    out_size = *data_size + sizeof(*data_size);
    ret = tpm_submit_cmd(locality, TPM_ORD_NV_READ_VALUE, in_size, &out_size);

#ifdef TPM_TRACE
    printf("TPM: read nv index %08x from offset %08x, return value = %08X\n",
           index, offset, ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: read nv index %08x offset %08x, return value = %08X\n",
               index, offset, ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    if ( out_size <= sizeof(*data_size) ) {
        *data_size = 0;
        return ret;
    }

    out_size -= sizeof(*data_size);
    reverse_copy(data_size, WRAPPER_OUT_BUF, sizeof(*data_size));
    *data_size = (*data_size > out_size) ? out_size : *data_size;
    if( *data_size > 0 )
        memcpy(data, WRAPPER_OUT_BUF + sizeof(*data_size), *data_size);

    return ret;
}

uint32_t tpm_nv_write_value(uint32_t locality, tpm_nv_index_t index,
                            uint32_t offset, const uint8_t *data,
                            uint32_t data_size)
{
    uint32_t ret, in_size = 0, out_size = 0;

    if ( data == NULL )
        return TPM_BAD_PARAMETER;
    if ( data_size == 0 || data_size > TPM_NV_WRITE_VALUE_DATA_SIZE_MAX )
        return TPM_BAD_PARAMETER;

    /* copy index, offset and *data_size into buf in reversed byte order */
    reverse_copy(WRAPPER_IN_BUF, &index, sizeof(index));
    in_size += sizeof(index);
    reverse_copy(WRAPPER_IN_BUF + in_size, &offset, sizeof(offset));
    in_size += sizeof(offset);
    reverse_copy(WRAPPER_IN_BUF + in_size, &data_size, sizeof(data_size));
    in_size += sizeof(data_size);
    memcpy(WRAPPER_IN_BUF + in_size, data, data_size);
    in_size += data_size;

    ret = tpm_submit_cmd(locality, TPM_ORD_NV_WRITE_VALUE,
                         in_size, &out_size);

#ifdef TPM_TRACE
    printf("TPM: write nv %08x, offset %08x, %08x bytes, return = %08X\n",
           index, offset, data_size, ret);
#endif
    if ( ret != TPM_SUCCESS )
        printf("TPM: write nv %08x, offset %08x, %08x bytes, return = %08X\n",
               index, offset, data_size, ret);

    return ret;
}

#define TPM_CAP_VERSION_VAL 0x1A

typedef uint16_t tpm_structure_tag_t;

typedef struct __attribute__ ((packed)) {
   uint8_t  major;
   uint8_t  minor;
   uint8_t  rev_major;
   uint8_t  rev_minor;
} tpm_version_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t tag;
    tpm_version_t       version;
    uint16_t            specLevel;
    uint8_t             errataRev;
    uint8_t             tpmVendorID[4];
    uint16_t            vendorSpecificSize;
    uint8_t             vendorSpecific[];
} tpm_cap_version_info_t;

/* get tpm module version */
uint32_t tpm_get_version(uint8_t *major, uint8_t *minor)
{
    uint32_t ret, in_size = 0, out_size;
    uint32_t cap_area = TPM_CAP_VERSION_VAL;
    uint32_t sub_cap_size = 0;
    uint32_t resp_size = 0;
    tpm_cap_version_info_t *cap_version;

    if ( major == NULL || minor == NULL )
        return TPM_BAD_PARAMETER;

    reverse_copy(WRAPPER_IN_BUF, &cap_area, sizeof(cap_area));
    in_size += sizeof(cap_area);
    reverse_copy(WRAPPER_IN_BUF+in_size, &sub_cap_size, sizeof(sub_cap_size));
    in_size += sizeof(sub_cap_size);

    out_size = sizeof(resp_size) + sizeof(tpm_cap_version_info_t);
    ret = tpm_submit_cmd(0, TPM_ORD_GET_CAPABILITY, in_size, &out_size);

#ifdef TPM_TRACE
    printf("TPM: get version, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: get version, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    reverse_copy(&resp_size, WRAPPER_OUT_BUF, sizeof(resp_size));
    cap_version = (tpm_cap_version_info_t *)
                            (WRAPPER_OUT_BUF + sizeof(resp_size));
    *major = cap_version->version.major;
    *minor = cap_version->version.minor;

    return ret;
}

#define HMAC_BLOCK_SIZE     64
#define HMAC_OUTPUT_SIZE    20

static bool hmac(const uint8_t key[HMAC_OUTPUT_SIZE], const uint8_t *msg,
                 uint32_t len, uint8_t md[HMAC_OUTPUT_SIZE])
{
    uint8_t ipad[HMAC_BLOCK_SIZE], opad[HMAC_BLOCK_SIZE];
    uint32_t i;
    SHA_CTX ctx;

    ASSERT(HMAC_OUTPUT_SIZE <= HMAC_BLOCK_SIZE);

    for ( i = 0; i < HMAC_BLOCK_SIZE; i++ ) {
        ipad[i] = 0x36;
        opad[i] = 0x5C;
    }

    for ( i = 0; i < HMAC_OUTPUT_SIZE; i++ ) {
        ipad[i] ^= key[i];
        opad[i] ^= key[i];
    }

    SHA1_Init(&ctx);
    SHA1_Update(&ctx, ipad, HMAC_BLOCK_SIZE);
    SHA1_Update(&ctx, msg, len);
    SHA1_Final(md, &ctx);

    SHA1_Init(&ctx);
    SHA1_Update(&ctx, opad, HMAC_BLOCK_SIZE);
    SHA1_Update(&ctx, md, HMAC_OUTPUT_SIZE);
    SHA1_Final(md, &ctx);

    return true;
}

typedef uint16_t tpm_entity_type_t;
typedef uint32_t tpm_authhandle_t;
typedef struct __attribute__ ((packed)) {
    uint8_t     nonce[20];
} tpm_nonce_t;

#define TPM_ET_SRK              0x0004
#define TPM_KH_SRK              0x40000000

typedef uint32_t tpm_key_handle_t;

typedef tpm_digest_t tpm_composite_hash_t;
typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t         tag;
    tpm_locality_selection_t    locality_at_creation;
    tpm_locality_selection_t    locality_at_release;
    tpm_pcr_selection_t         creation_pcr_selection;
    tpm_pcr_selection_t         release_pcr_selection;
    tpm_composite_hash_t        digest_at_creation;
    tpm_composite_hash_t        digest_at_release;
} tpm_pcr_info_long_t;

typedef uint8_t tpm_authdata_t[20];
typedef tpm_authdata_t tpm_encauth_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t         tag;
    tpm_entity_type_t           et;
    uint32_t                    seal_info_size;
} tpm_stored_data12_header_t;

typedef struct __attribute__ ((packed)) {
    tpm_stored_data12_header_t  header;
    uint32_t                    enc_data_size;
    uint8_t                     enc_data[];
} tpm_stored_data12_short_t;

typedef struct __attribute__ ((packed)) {
    tpm_stored_data12_header_t  header;
    tpm_pcr_info_long_t         seal_info;
    uint32_t                    enc_data_size;
    uint8_t                     enc_data[];
} tpm_stored_data12_t;

#define UNLOAD_INTEGER(buf, offset, var) {\
    reverse_copy(buf + offset, &(var), sizeof(var));\
    offset += sizeof(var);\
}

#define UNLOAD_BLOB(buf, offset, blob, size) {\
        memcpy(buf + offset, blob, size); \
    offset += size;\
}

#define UNLOAD_BLOB_TYPE(buf, offset, blob) \
    UNLOAD_BLOB(buf, offset, blob, sizeof(*(blob)))

#define UNLOAD_PCR_SELECTION(buf, offset, sel) {\
    UNLOAD_INTEGER(buf, offset, (sel)->size_of_select);\
    UNLOAD_BLOB(buf, offset, (sel)->pcr_select, (sel)->size_of_select);\
}

#define UNLOAD_PCR_INFO_LONG(buf, offset, info) {\
    UNLOAD_INTEGER(buf, offset, (info)->tag);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_creation);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_release);\
    UNLOAD_PCR_SELECTION(buf, offset, &(info)->creation_pcr_selection);\
    UNLOAD_PCR_SELECTION(buf, offset, &(info)->release_pcr_selection);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_creation);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_release);\
}

#define UNLOAD_STORED_DATA12(buf, offset, hdr) {\
   UNLOAD_INTEGER(buf, offset, ((const tpm_stored_data12_header_t *)(hdr))->tag);\
   UNLOAD_INTEGER(buf, offset, ((const tpm_stored_data12_header_t *)(hdr))->et);\
   UNLOAD_INTEGER(buf, offset,\
                  ((const tpm_stored_data12_header_t *)(hdr))->seal_info_size);\
   if ( ((const tpm_stored_data12_header_t *)(hdr))->seal_info_size == 0 ) {\
       UNLOAD_INTEGER(buf, offset,\
                      ((const tpm_stored_data12_short_t *)hdr)->enc_data_size);\
       UNLOAD_BLOB(buf, offset,\
                   ((const tpm_stored_data12_short_t *)hdr)->enc_data,\
                   ((const tpm_stored_data12_short_t *)hdr)->enc_data_size);\
   }\
   else {\
       UNLOAD_PCR_INFO_LONG(buf, offset,\
                            &((const tpm_stored_data12_t *)hdr)->seal_info);\
       UNLOAD_INTEGER(buf, offset,\
                      ((const tpm_stored_data12_t *)hdr)->enc_data_size);\
       UNLOAD_BLOB(buf, offset,\
                   ((const tpm_stored_data12_t *)hdr)->enc_data,\
                   ((const tpm_stored_data12_t *)hdr)->enc_data_size);\
   }\
}

#define LOAD_INTEGER(buf, offset, var) {\
    reverse_copy(&(var), buf + offset, sizeof(var));\
    offset += sizeof(var);\
}

#define LOAD_BLOB(buf, offset, blob, size) {\
    memcpy(blob, buf + offset, size);\
    offset += size;\
}

#define LOAD_BLOB_TYPE(buf, offset, blob) \
    LOAD_BLOB(buf, offset, blob, sizeof(*(blob)))

#define LOAD_PCR_SELECTION(buf, offset, sel) {\
    LOAD_INTEGER(buf, offset, (sel)->size_of_select);\
    LOAD_BLOB(buf, offset, (sel)->pcr_select, (sel)->size_of_select);\
}

#define LOAD_PCR_INFO_LONG(buf, offset, info) {\
    LOAD_INTEGER(buf, offset, (info)->tag);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_creation);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_release);\
    LOAD_PCR_SELECTION(buf, offset, &(info)->creation_pcr_selection);\
    LOAD_PCR_SELECTION(buf, offset, &(info)->release_pcr_selection);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_creation);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_release);\
}

#define LOAD_STORED_DATA12(buf, offset, hdr) {\
   LOAD_INTEGER(buf, offset, ((tpm_stored_data12_header_t *)(hdr))->tag);\
   LOAD_INTEGER(buf, offset, ((tpm_stored_data12_header_t *)(hdr))->et);\
   LOAD_INTEGER(buf, offset, \
                ((tpm_stored_data12_header_t *)(hdr))->seal_info_size);\
   if ( ((tpm_stored_data12_header_t *)(hdr))->seal_info_size == 0 ) {\
       LOAD_INTEGER(buf, offset,\
                    ((tpm_stored_data12_short_t *)hdr)->enc_data_size);\
       LOAD_BLOB(buf, offset,\
                 ((tpm_stored_data12_short_t *)hdr)->enc_data,\
                 ((tpm_stored_data12_short_t *)hdr)->enc_data_size);\
   }\
   else {\
       LOAD_PCR_INFO_LONG(buf, offset,\
                          &((tpm_stored_data12_t *)hdr)->seal_info);\
       LOAD_INTEGER(buf, offset,\
                    ((tpm_stored_data12_t *)hdr)->enc_data_size);\
       LOAD_BLOB(buf, offset,\
                 ((tpm_stored_data12_t *)hdr)->enc_data,\
                 ((tpm_stored_data12_t *)hdr)->enc_data_size);\
   }\
}

static uint32_t tpm_oiap(uint32_t locality, tpm_authhandle_t *hauth,
                         tpm_nonce_t *nonce_even)
{
    uint32_t ret, offset, out_size;

    if ( hauth == NULL || nonce_even == NULL )
        return TPM_BAD_PARAMETER;

    offset = 0;

    out_size = sizeof(*hauth) + sizeof(*nonce_even);

    ret = tpm_submit_cmd(locality, TPM_ORD_OIAP, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: start OIAP, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: start OIAP, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    offset = 0;
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *hauth);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even);

    return ret;
}

static uint32_t tpm_osap(uint32_t locality, tpm_entity_type_t ent_type,
                         uint32_t ent_value, const tpm_nonce_t *odd_osap,
                         tpm_authhandle_t *hauth, tpm_nonce_t *nonce_even,
                         tpm_nonce_t *even_osap)
{
    uint32_t ret, offset, out_size;

    if ( odd_osap == NULL || hauth == NULL ||
         nonce_even == NULL || even_osap == NULL )
        return TPM_BAD_PARAMETER;

    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, ent_type);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, ent_value);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, odd_osap);

    out_size = sizeof(*hauth) + sizeof(*nonce_even) + sizeof(*even_osap);
    ret = tpm_submit_cmd(locality, TPM_ORD_OSAP, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: start OSAP, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: start OSAP, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    offset = 0;
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *hauth);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, even_osap);

    return ret;
}

static uint32_t _tpm_seal(uint32_t locality, tpm_key_handle_t hkey,
                  const tpm_encauth_t *enc_auth, uint32_t pcr_info_size,
                  const tpm_pcr_info_long_t *pcr_info, uint32_t in_data_size,
                  const uint8_t *in_data,
                  tpm_authhandle_t hauth, const tpm_nonce_t *nonce_odd,
                  uint8_t *cont_session, const tpm_authdata_t *pub_auth,
                  uint32_t *sealed_data_size, uint8_t *sealed_data,
                  tpm_nonce_t *nonce_even, tpm_authdata_t *res_auth)
{
    uint32_t ret, offset, out_size;

    if ( enc_auth == NULL || pcr_info == NULL || in_data == NULL ||
         nonce_odd == NULL || cont_session == NULL || pub_auth == NULL ||
         sealed_data_size == NULL || sealed_data == NULL ||
         nonce_even == NULL || res_auth == NULL ) {
        printf("TPM: _tpm_seal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hkey);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, enc_auth);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, pcr_info_size);
    UNLOAD_PCR_INFO_LONG(WRAPPER_IN_BUF, offset, pcr_info);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, in_data_size);
    UNLOAD_BLOB(WRAPPER_IN_BUF, offset, in_data, in_data_size);

    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hauth);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, nonce_odd);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, *cont_session);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, pub_auth);

    out_size = WRAPPER_OUT_MAX_SIZE;

    ret = tpm_submit_cmd_auth1(locality, TPM_ORD_SEAL, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: seal data, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: seal data, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    if ( *sealed_data_size <
         ( out_size - sizeof(*nonce_even) - sizeof(*cont_session)
           - sizeof(*res_auth) ) ) {
        printf("TPM: sealed blob is too small\n");
        return TPM_NOSPACE;
    }

    offset = 0;
    LOAD_STORED_DATA12(WRAPPER_OUT_BUF, offset, sealed_data);
    *sealed_data_size = offset;
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even);
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *cont_session);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, res_auth);

    return ret;
}

static uint32_t _tpm_unseal(uint32_t locality, tpm_key_handle_t hkey,
                    const uint8_t *in_data,
                    tpm_authhandle_t hauth, const tpm_nonce_t *nonce_odd,
                    uint8_t *cont_session, const tpm_authdata_t *auth,
                    tpm_authhandle_t hauth_d, const tpm_nonce_t *nonce_odd_d,
                    uint8_t *cont_session_d, const tpm_authdata_t *auth_d,
                    uint32_t *secret_size, uint8_t *secret,
                    tpm_nonce_t *nonce_even, tpm_authdata_t *res_auth,
                    tpm_nonce_t *nonce_even_d, tpm_authdata_t *res_auth_d)
{
    uint32_t ret, offset, out_size;

    if ( in_data == NULL || nonce_odd == NULL || cont_session == NULL ||
         auth == NULL || nonce_odd_d == NULL || cont_session_d == NULL ||
         auth_d == NULL || secret_size == NULL || secret == NULL ||
         nonce_even == NULL || res_auth == NULL || nonce_even_d == NULL ||
         res_auth_d == NULL ) {
        printf("TPM: _tpm_unseal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hkey);
    UNLOAD_STORED_DATA12(WRAPPER_IN_BUF, offset, in_data);

    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hauth);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, nonce_odd);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, *cont_session);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, auth);

    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hauth_d);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, nonce_odd_d);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, *cont_session_d);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, auth_d);

    out_size = WRAPPER_OUT_MAX_SIZE;

    ret = tpm_submit_cmd_auth2(locality, TPM_ORD_UNSEAL, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: unseal data, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: unseal data, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    if ( *secret_size <
         ( out_size - sizeof(*secret_size) - sizeof(*nonce_even)
           - sizeof(*cont_session) - sizeof(*res_auth) - sizeof(*nonce_even_d)
           - sizeof(*cont_session_d) - sizeof(*res_auth_d) ) ) {
        printf("TPM: unsealed data too small\n");
        return TPM_NOSPACE;
    }

    offset = 0;
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *secret_size);
    LOAD_BLOB(WRAPPER_OUT_BUF, offset, secret, *secret_size);

    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even);
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *cont_session);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, res_auth);

    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even_d);
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *cont_session_d);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, res_auth_d);

    return ret;
}

#define XOR_BLOB_TYPE(data, pad) {\
    uint32_t i;                                 \
    for ( i = 0; i < sizeof(*(data)); i++ ) \
        ((uint8_t *)data)[i] ^= ((uint8_t *)pad)[i % sizeof(*(pad))];\
}

static const tpm_authdata_t srk_authdata =
    {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
static const tpm_authdata_t blob_authdata =
    {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

static uint32_t _tpm_wrap_seal(uint32_t locality,
                              const tpm_pcr_info_long_t *pcr_info,
                              uint32_t in_data_size, const uint8_t *in_data,
                              uint32_t *sealed_data_size, uint8_t *sealed_data)
{
    uint32_t ret;
    tpm_nonce_t odd_osap, even_osap, nonce_even, nonce_odd;
    tpm_authhandle_t hauth;
    tpm_authdata_t shared_secret, pub_auth, res_auth;
    tpm_encauth_t enc_auth;
    uint8_t cont_session = false;
    tpm_key_handle_t hkey = TPM_KH_SRK;
    uint32_t pcr_info_size = sizeof(*pcr_info);
    uint32_t offset;
    uint32_t ordinal = TPM_ORD_SEAL;
    tpm_digest_t digest;

    /* skip generate nonce for odd_osap, just use the random value in stack */

    /* establish a osap session */
    ret = tpm_osap(locality, TPM_ET_SRK, TPM_KH_SRK, &odd_osap, &hauth,
                   &nonce_even, &even_osap);
    if ( ret != TPM_SUCCESS )
            return ret;

    /* calculate the shared secret
       shared-secret = HMAC(srk_auth, even_osap || odd_osap) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &even_osap);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &odd_osap);
    hmac((uint8_t *)&srk_authdata, WRAPPER_IN_BUF, offset,
         (uint8_t *)&shared_secret);

    /* generate ecrypted authdata for data
       enc_auth = XOR(authdata, sha1(shared_secret || last_even_nonce)) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &shared_secret);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_even);
    sha1_buffer(WRAPPER_IN_BUF, offset, (uint8_t *)&digest);
    memcpy(&enc_auth, &blob_authdata, sizeof(blob_authdata));
    XOR_BLOB_TYPE(&enc_auth, &digest);

    /* skip generate nonce for nonce_odd, just use the random value in stack */

    /* calculate authdata */
    /* in_param_digest = sha1(1S ~ 6S) */
    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, ordinal);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &enc_auth);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, pcr_info_size);
    UNLOAD_PCR_INFO_LONG(WRAPPER_IN_BUF, offset, pcr_info);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, in_data_size);
    UNLOAD_BLOB(WRAPPER_IN_BUF, offset, in_data, in_data_size);
    sha1_buffer(WRAPPER_IN_BUF, offset, (uint8_t *)&digest);

    /* authdata = hmac(key, in_param_digest || auth_params) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &digest);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_even);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_odd);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, cont_session);
    hmac((uint8_t *)&shared_secret, WRAPPER_IN_BUF, offset,
         (uint8_t *)&pub_auth);

    /* call the simple seal function */
    ret = _tpm_seal(locality, hkey, (const tpm_encauth_t *)&enc_auth,
                    pcr_info_size, pcr_info, in_data_size, in_data,
                    hauth, &nonce_odd, &cont_session,
                    (const tpm_authdata_t *)&pub_auth,
                    sealed_data_size, sealed_data,
                    &nonce_even, &res_auth);

    /* skip check for res_auth */

    return ret;
}

static uint32_t _tpm_wrap_unseal(uint32_t locality, const uint8_t *in_data,
                                 uint32_t *secret_size, uint8_t *secret)
{
    uint32_t ret;
    tpm_nonce_t odd_osap, even_osap;
    tpm_nonce_t nonce_even, nonce_odd, nonce_even_d, nonce_odd_d;
    tpm_authhandle_t hauth, hauth_d;
    tpm_authdata_t shared_secret;
    tpm_authdata_t pub_auth, res_auth, pub_auth_d, res_auth_d;
    uint8_t cont_session = false, cont_session_d = false;
    tpm_key_handle_t hkey = TPM_KH_SRK;
    uint32_t offset;
    uint32_t ordinal = TPM_ORD_UNSEAL;
    tpm_digest_t digest;

    /* skip generate nonce for odd_osap, just use the random value in stack */

    /* establish a osap session */
    ret = tpm_osap(locality, TPM_ET_SRK, TPM_KH_SRK, &odd_osap, &hauth,
                   &nonce_even, &even_osap);
    if ( ret != TPM_SUCCESS )
            return ret;

    /* calculate the shared secret
       shared-secret = HMAC(auth, even_osap || odd_osap) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &even_osap);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &odd_osap);
    hmac((uint8_t *)&srk_authdata, WRAPPER_IN_BUF, offset,
         (uint8_t *)&shared_secret);

    /* establish a oiap session */
    ret = tpm_oiap(locality, &hauth_d, &nonce_even_d);
    if ( ret != TPM_SUCCESS )
            return ret;

    /* skip generate nonce_odd & nonce_odd_d, just use the random values */

    /* calculate authdata */
    /* in_param_digest = sha1(1S ~ 6S) */
    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, ordinal);
    UNLOAD_STORED_DATA12(WRAPPER_IN_BUF, offset, in_data);
    sha1_buffer(WRAPPER_IN_BUF, offset, (uint8_t *)&digest);

    /* authdata1 = hmac(key, in_param_digest || auth_params1) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &digest);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_even);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_odd);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, cont_session);
    hmac((uint8_t *)&shared_secret, WRAPPER_IN_BUF, offset,
         (uint8_t *)&pub_auth);

    /* authdata2 = hmac(key, in_param_digest || auth_params2) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &digest);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_even_d);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_odd_d);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, cont_session_d);
    hmac((uint8_t *)&blob_authdata, WRAPPER_IN_BUF, offset,
         (uint8_t *)&pub_auth_d);

    /* call the simple seal function */
    ret = _tpm_unseal(locality, hkey, in_data,
                      hauth, &nonce_odd, &cont_session,
                      (const tpm_authdata_t *)&pub_auth,
                      hauth_d, &nonce_odd_d, &cont_session_d,
                      (const tpm_authdata_t *)&pub_auth_d,
                      secret_size, secret,
                      &nonce_even, &res_auth, &nonce_even_d, &res_auth_d);

    /* skip check for res_auth */

    return ret;
}

static bool init_pcr_info(uint32_t locality,
                          tpm_locality_selection_t release_locs,
                          uint32_t nr_create, const uint8_t indcs_create[],
                          uint32_t nr_release, const uint8_t indcs_release[],
                          const tpm_pcr_value_t *values_release[],
                          tpm_pcr_info_long_t *pcr_info)
{
    uint32_t offset;
    uint32_t i, blob_size;
    static tpm_locality_selection_t localities[TPM_NR_LOCALITIES] = {
        TPM_LOC_ZERO, TPM_LOC_ONE, TPM_LOC_TWO, TPM_LOC_THREE, TPM_LOC_FOUR
    };


    if ( (release_locs & TPM_LOC_RSVD) != 0 )
        return TPM_BAD_PARAMETER;
    if ( pcr_info == NULL )
        return TPM_BAD_PARAMETER;
    if ( locality >= TPM_NR_LOCALITIES )
        return TPM_BAD_PARAMETER;
    if ( indcs_create == NULL )
        nr_create = 0;
    if ( indcs_release == NULL || values_release == NULL )
        nr_release = 0;
    for ( i = 0; i < nr_create; i++ )
        if ( indcs_create[i] >= TPM_NR_PCRS )
            return TPM_BAD_PARAMETER;
    for ( i = 0; i < nr_release; i++ ) {
        if ( indcs_release[i] >= TPM_NR_PCRS || values_release[i] == NULL )
            return TPM_BAD_PARAMETER;
    }

    memset(pcr_info, 0, sizeof(*pcr_info));
    pcr_info->tag = TPM_TAG_PCR_INFO_LONG;
    pcr_info->locality_at_creation = localities[locality];
    pcr_info->locality_at_release = release_locs;
    pcr_info->creation_pcr_selection.size_of_select = 3;
    for ( i = 0; i < nr_create; i++ )
        pcr_info->creation_pcr_selection.pcr_select[indcs_create[i]/8] |=
            1 << (indcs_create[i] % 8);
    pcr_info->release_pcr_selection.size_of_select = 3;
    for ( i = 0; i < nr_release; i++ )
        pcr_info->release_pcr_selection.pcr_select[indcs_release[i]/8] |=
            1 << (indcs_release[i] % 8);

    if ( nr_release > 0 ) {
        offset = 0;
        UNLOAD_PCR_SELECTION(WRAPPER_IN_BUF, offset,
                             &pcr_info->release_pcr_selection);
        blob_size = sizeof(tpm_pcr_value_t) * nr_release;
        UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, blob_size);
        for ( i = 0; i < nr_release; i++ )
            UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, values_release[i]);
        sha1_buffer(WRAPPER_IN_BUF, offset,
                    (uint8_t *)&pcr_info->digest_at_release);
    }

    return true;
}

uint32_t tpm_seal(uint32_t locality, tpm_locality_selection_t release_locs,
                  uint32_t pcr_nr_create, const uint8_t pcr_indcs_create[],
                  uint32_t pcr_nr_release, const uint8_t pcr_indcs_release[],
                  const tpm_pcr_value_t *pcr_values_release[],
                  uint32_t in_data_size, const uint8_t *in_data,
                  uint32_t *sealed_data_size, uint8_t *sealed_data)
{
    uint32_t ret;
    tpm_pcr_info_long_t pcr_info;

    if ( locality >= TPM_NR_LOCALITIES ||
         in_data_size == 0 || in_data == NULL ||
         sealed_data_size == NULL || sealed_data == NULL ||
         *sealed_data_size == 0 ) {
        printf("TPM: tpm_seal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    if ( !init_pcr_info(locality, release_locs, pcr_nr_create,
                        pcr_indcs_create, pcr_nr_release, pcr_indcs_release,
                        pcr_values_release, &pcr_info) ) {
        printf("TPM: tpm_seal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    ret = _tpm_wrap_seal(locality, &pcr_info, in_data_size, in_data,
                         sealed_data_size, sealed_data);

    return ret;
}

static bool check_sealed_data(uint32_t size, const uint8_t *data)
{
    if ( size < sizeof(tpm_stored_data12_header_t) )
        return false;
    if ( ((const tpm_stored_data12_header_t *)data)->tag != TPM_TAG_STORED_DATA12 )
        return false;

    if ( ((const tpm_stored_data12_header_t *)data)->seal_info_size == 0 ) {
        const tpm_stored_data12_short_t *data12_s;

        if ( size < sizeof(*data12_s) )
            return false;
        data12_s = (const tpm_stored_data12_short_t *)data;
        if ( size != sizeof(*data12_s) + data12_s->enc_data_size )
            return false;
    }
    else {
        const tpm_stored_data12_t *data12;

        if ( size < sizeof(*data12) )
            return false;
        data12 = (const tpm_stored_data12_t *)data;
        if ( size != sizeof(*data12) + data12->enc_data_size )
            return false;
    }

    return true;
}

uint32_t tpm_unseal(uint32_t locality,
                    uint32_t sealed_data_size, const uint8_t *sealed_data,
                    uint32_t *secret_size, uint8_t *secret)
{
    uint32_t ret;

    if ( sealed_data == NULL ||
         secret_size == NULL || secret == NULL ) {
        printf("TPM: tpm_unseal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    if ( !check_sealed_data(sealed_data_size, sealed_data) ) {
        printf("TPM: tpm_unseal() blob invalid\n");
        return TPM_BAD_PARAMETER;
    }

    ret = _tpm_wrap_unseal(locality, sealed_data, secret_size, secret);

    return ret;
}

static void calc_pcr_composition(uint32_t nr, const uint8_t indcs[],
                                 const tpm_pcr_value_t *values[],
                                 tpm_composite_hash_t *composite)
{
    uint32_t i, offset, blob_size;
    tpm_pcr_selection_t sel;

    if ( nr == 0 || indcs == NULL || values == NULL || composite == NULL)
        return;

    sel.size_of_select = 3;
    sel.pcr_select[0] = sel.pcr_select[1] = sel.pcr_select[2] = 0;
    for ( i = 0; i < nr; i++ )
        sel.pcr_select[indcs[i]/8] |= 1 << (indcs[i] % 8);

    offset = 0;
    UNLOAD_PCR_SELECTION(WRAPPER_IN_BUF, offset, &sel);
    blob_size = sizeof(tpm_pcr_value_t) * nr;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, blob_size);
    for ( i = 0; i < nr; i++ )
        UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, values[i]);
    sha1_buffer(WRAPPER_IN_BUF, offset, (uint8_t *)composite);
}

static tpm_composite_hash_t *get_cre_pcr_composite(uint8_t *data)
{
    if ( ((tpm_stored_data12_header_t *)data)->seal_info_size == 0 )
        return NULL;
    else
        return &((tpm_stored_data12_t *)data)->seal_info.digest_at_creation;
}

bool tpm_cmp_creation_pcrs(uint32_t pcr_nr_create,
                           const uint8_t pcr_indcs_create[],
                           const tpm_pcr_value_t *pcr_values_create[],
                           uint32_t sealed_data_size, uint8_t *sealed_data)
{
    uint32_t i;
    tpm_composite_hash_t composite = {{0,}}, *cre_composite;

    if ( pcr_indcs_create == NULL )
        pcr_nr_create = 0;
    for ( i = 0; i < pcr_nr_create; i++ ) {
        if ( pcr_indcs_create[i] >= TPM_NR_PCRS )
            return false;
    }
    if ( !check_sealed_data(sealed_data_size, sealed_data) ) {
        printf("TPM: Bad blob.\n");
        return false;
    }

    if ( pcr_nr_create > 0 )
        calc_pcr_composition(pcr_nr_create, pcr_indcs_create,
                             pcr_values_create, &composite);

    cre_composite = get_cre_pcr_composite(sealed_data);
    if ( cre_composite == NULL )
        return false;
    if ( memcmp((uint8_t*)&composite, (uint8_t*)cre_composite, sizeof(composite)) ) {
        printf("TPM: Not equal to creation composition:\n");
        print_hex(NULL, (uint8_t *)&composite, sizeof(composite));
        print_hex(NULL, (uint8_t *)cre_composite, sizeof(composite));
        return false;
    }

    return true;
}

typedef uint32_t tpm_capability_area_t;

#define TPM_CAP_NV_INDEX    0x00000011

static uint32_t tpm_get_capability(
                  uint32_t locality, tpm_capability_area_t cap_area,
                  uint32_t sub_cap_size, const uint8_t *sub_cap,
                  uint32_t *resp_size, uint8_t *resp)
{
    uint32_t ret, offset, out_size;

    if ( sub_cap == NULL || resp_size == NULL || resp == NULL ) {
        printf("TPM: tpm_get_capability() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, cap_area);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, sub_cap_size);
    UNLOAD_BLOB(WRAPPER_IN_BUF, offset, sub_cap, sub_cap_size);

    out_size = sizeof(*resp_size) + *resp_size;

    ret = tpm_submit_cmd(locality, TPM_ORD_GET_CAPABILITY, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: get capability, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: get capability, return value = %08X\n", ret);
        return ret;
    }

    offset = 0;
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *resp_size);
    if ( out_size < sizeof(*resp_size) + *resp_size ) {
        printf("TPM: capability response too small\n");
        return TPM_FAIL;
    }
    LOAD_BLOB(WRAPPER_OUT_BUF, offset, resp, *resp_size);

    return ret;
}

typedef struct __attribute__ ((packed)) {
    tpm_pcr_selection_t         pcr_selection;
    tpm_locality_selection_t    locality_at_release;
    tpm_composite_hash_t        digest_at_release;
} tpm_pcr_info_short_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t tag;
    uint32_t            attributes;
} tpm_nv_attributes_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t     tag;
    tpm_nv_index_t          nv_index;
    tpm_pcr_info_short_t    pcr_info_read;
    tpm_pcr_info_short_t    pcr_info_write;
    tpm_nv_attributes_t     permission;
    uint8_t                 b_read_st_clear;
    uint8_t                 b_write_st_clear;
    uint8_t                 b_write_define;
    uint32_t                data_size;
} tpm_nv_data_public_t;

uint32_t tpm_get_nvindex_size(uint32_t locality,
                              tpm_nv_index_t index, uint32_t *size)
{
    uint32_t ret, offset, resp_size;
    uint8_t sub_cap[sizeof(index)];
    uint8_t resp[sizeof(tpm_nv_data_public_t)];
    tpm_nv_index_t idx;

    if ( size == NULL ) {
        printf("TPM: tpm_get_nvindex_size() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(sub_cap, offset, index);

    resp_size = sizeof(resp);
    ret = tpm_get_capability(locality, TPM_CAP_NV_INDEX, sizeof(sub_cap),
                             sub_cap, &resp_size, resp);

#ifdef TPM_TRACE
    printf("TPM: get nvindex size, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: fail to get public data of 0x%08X in TPM NV\n", index);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, resp, resp_size);
    }
#endif

    /* check size */
    if ( resp_size == 0 ) {
        printf("TPM: Index 0x%08X does not exist\n", index);
        return TPM_BADINDEX;
    }

    /* check index */
    offset = sizeof(tpm_structure_tag_t);
    LOAD_INTEGER(resp, offset, idx);
#ifdef TPM_TRACE
    printf("TPM: get index value = %08X\n", idx);
#endif

    if ( idx != index ) {
        printf("TPM: Index 0x%08X is not the one expected 0x%08X\n",
               idx, index);
        return TPM_BADINDEX;
    }

    if ( resp_size != sizeof(resp) ) {
        printf("TPM: public data size of Index 0x%08X responsed incorrect\n",
               index);
        return TPM_FAIL;
    }

    offset = resp_size - sizeof(uint32_t);
    LOAD_INTEGER(resp, offset, *size);

    return ret;
}

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t tag;
    uint8_t disable;
    uint8_t ownership;
    uint8_t deactivated;
    uint8_t read_pubek;
    uint8_t disable_owner_clear;
    uint8_t allow_maintenance;
    uint8_t physical_presence_lifetime_lock;
    uint8_t physical_presence_hw_enable;
    uint8_t physical_presence_cmd_enable;
    uint8_t cekp_used;
    uint8_t tpm_post;
    uint8_t tpm_post_lock;
    uint8_t fips;
    uint8_t operator;
    uint8_t enable_revoke_ek;
    uint8_t nv_locked;
    uint8_t read_srk_pub;
    uint8_t tpm_established;
    uint8_t maintenance_done;
    uint8_t disable_full_da_logic_info;
} tpm_permanent_flags_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t tag;
    uint8_t deactivated;
    uint8_t disable_force_clear;
    uint8_t physical_presence;
    uint8_t phycical_presence_lock;
    uint8_t b_global_lock;
} tpm_stclear_flags_t;

#define TPM_CAP_FLAG            0x00000004
#define TPM_CAP_FLAG_PERMANENT  0x00000108
#define TPM_CAP_FLAG_VOLATILE   0x00000109

static uint32_t tpm_get_flags(uint32_t locality, uint32_t flag_id,
                       uint8_t *flags, uint32_t flag_size)
{
    uint32_t ret, offset, resp_size;
    uint8_t sub_cap[sizeof(flag_id)];
    tpm_structure_tag_t tag;

    if ( flags == NULL ) {
        printf("TPM: tpm_get_flags() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(sub_cap, offset, flag_id);

    resp_size = flag_size;
    ret = tpm_get_capability(locality, TPM_CAP_FLAG, sizeof(sub_cap),
                             sub_cap, &resp_size, flags);

#ifdef TPM_TRACE
    printf("TPM: get flags %08X, return value = %08X\n", flag_id, ret);
#endif
    if ( ret != TPM_SUCCESS )
        return ret;

    /* 1.2 spec, main part 2, rev 103 add one more byte to permanent flags, to
       be backward compatible, not assume all expected bytes can be gotten */
    if ( resp_size > flag_size ) {
        printf("TPM: tpm_get_flags() response size too small\n");
        return TPM_FAIL;
    }

    offset = 0;
    LOAD_INTEGER(flags, offset, tag);
    offset = 0;
    UNLOAD_BLOB_TYPE(flags, offset, &tag);

    return ret;
}

#define TPM_CAP_PROPERTY          0x00000005
#define TPM_CAP_PROP_TIS_TIMEOUT  0x00000115

static uint32_t tpm_get_timeout(uint32_t locality,
                       uint8_t *prop, uint32_t prop_size)
{
    uint32_t ret, offset, resp_size, prop_id = TPM_CAP_PROP_TIS_TIMEOUT;
    uint8_t sub_cap[sizeof(prop_id)];
    uint32_t resp[4];

    if ( (prop == NULL) || (prop_size < sizeof(resp)) ) {
        printf("TPM: tpm_get_timeout() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(sub_cap, offset, prop_id);

    resp_size = prop_size;
    ret = tpm_get_capability(locality, TPM_CAP_PROPERTY, sizeof(sub_cap),
                             sub_cap, &resp_size, prop);

#ifdef TPM_TRACE
    printf("TPM: get prop %08X, return value = %08X\n", prop_id, ret);
#endif
    if ( ret != TPM_SUCCESS )
        return ret;

    if ( resp_size != prop_size ) {
        printf("TPM: tpm_get_property() response size incorrect\n");
        return TPM_FAIL;
    }

    offset = 0;
    LOAD_INTEGER(prop, offset, resp);
    offset = 0;
    UNLOAD_BLOB_TYPE(prop, offset, &resp);

    return ret;
}

bool release_locality(uint32_t locality)
{
    uint32_t i;
    tpm_reg_access_t reg_acc;
#ifdef TPM_TRACE
    printf("TPM: releasing locality %u\n", locality);
#endif

    if ( !tpm_validate_locality(locality) )
        return true;

    read_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
    if ( reg_acc.active_locality == 0 )
        return true;

    /* make inactive by writing a 1 */
    reg_acc._raw[0] = 0;
    reg_acc.active_locality = 1;
    write_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);

    i = 0;
    do {
        read_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
        if ( reg_acc.active_locality == 0 )
            return true;
        else
            cpu_relax();
        i++;
    } while ( i <= TPM_ACTIVE_LOCALITY_TIME_OUT );

    printf("TPM: access reg release locality timeout\n");
    return false;
}

bool prepare_tpm(void)
{
    /*
     * must ensure TPM_ACCESS_0.activeLocality bit is clear
     * (: locality is not active)
     */

    return release_locality(0);
}

/* ensure TPM is ready to accept commands */
bool is_tpm_ready(uint32_t locality)
{
    tpm_permanent_flags_t pflags;
    tpm_stclear_flags_t vflags;
    uint32_t timeout[4];
    uint32_t ret;

    if ( !tpm_validate_locality(locality) ) {
        printf("TPM is not available.\n");
        return false;
    }

    /* make sure tpm is not disabled/deactivated */
    memset(&pflags, 0, sizeof(pflags));
    ret = tpm_get_flags(locality, TPM_CAP_FLAG_PERMANENT,
                        (uint8_t *)&pflags, sizeof(pflags));
    if ( ret != TPM_SUCCESS ) {
        printf("TPM is disabled or deactivated.\n");
        return false;
    }
    if ( pflags.disable ) {
        printf("TPM is disabled.\n");
        return false;
    }

    memset(&vflags, 0, sizeof(vflags));
    ret = tpm_get_flags(locality, TPM_CAP_FLAG_VOLATILE,
                        (uint8_t *)&vflags, sizeof(vflags));
    if ( ret != TPM_SUCCESS ) {
        printf("TPM is disabled or deactivated.\n");
        return false;
    }
    if ( vflags.deactivated ) {
        printf("TPM is deactivated.\n");
        return false;
    }

    printf("TPM is ready\n");
    printf("TPM nv_locked: %s\n", (pflags.nv_locked != 0) ? "TRUE" : "FALSE");

    /* get tpm timeout values */
    ret = tpm_get_timeout(locality, (uint8_t *)&timeout, sizeof(timeout));
    if ( ret != TPM_SUCCESS )
        printf("TPM timeout values are not achieved, "
               "default values will be used.\n");
    else {
        /*
         * timeout_x represents the number of milliseconds for the timeout
         * and timeout[x] represents the number of microseconds.
         */
        g_timeout.timeout_a = timeout[0]/1000;
        g_timeout.timeout_b = timeout[1]/1000;
        g_timeout.timeout_c = timeout[2]/1000;
        g_timeout.timeout_d = timeout[3]/1000;
        printf("TPM timeout values: A: %u, B: %u, C: %u, D: %u\n",
               g_timeout.timeout_a, g_timeout.timeout_b, g_timeout.timeout_c,
               g_timeout.timeout_d);
        /*
         * if any timeout values are less than default values, set to default
         * value (due to bug with some TPMs)
         */
        if ( g_timeout.timeout_a < TIMEOUT_A ) g_timeout.timeout_a = TIMEOUT_A;
        if ( g_timeout.timeout_b < TIMEOUT_B ) g_timeout.timeout_b = TIMEOUT_B;
        if ( g_timeout.timeout_c < TIMEOUT_C ) g_timeout.timeout_c = TIMEOUT_C;
        if ( g_timeout.timeout_d < TIMEOUT_D ) g_timeout.timeout_d = TIMEOUT_D;
    }

    return true;
}

uint32_t tpm_save_state(uint32_t locality)
{
    uint32_t ret, offset, out_size;
    uint32_t retries = 0;

    do {
        offset = 0;
        out_size = 0;

        ret = tpm_submit_cmd(locality, TPM_ORD_SAVE_STATE, offset, &out_size);
        if ( retries == 0 )
            printf("TPM: save state, return value = %08X\n", ret);
        else if ( retries == 1 )
            printf("retrying command: .");
        else
            printf(".");

        if ( ret != TPM_RETRY )
            break;

        retries++;
        ASSERT(false); // XXX need delay support
        //delay(100);
    } while ( retries < MAX_SAVESTATE_RETRIES );
    if ( retries >= MAX_SAVESTATE_RETRIES )
        printf("TIMEOUT!");
    if ( retries > 0 )
        printf("\n");

    return ret;
}

uint32_t tpm_get_random(uint32_t locality, uint8_t *random_data,
                        uint32_t *data_size)
{
    uint32_t ret, in_size = 0, out_size, requested_size;
    static bool first_attempt;
    uint32_t second_size;
    
    if ( random_data == NULL || data_size == NULL )
        return TPM_BAD_PARAMETER;
    if ( *data_size == 0 )
        return TPM_BAD_PARAMETER;

    first_attempt = true;
    requested_size = *data_size;

    /* copy the *data_size into buf in reversed byte order */
    reverse_copy(WRAPPER_IN_BUF + in_size, data_size, sizeof(*data_size));
    in_size += sizeof(*data_size);

    out_size = *data_size + sizeof(*data_size);
    ret = tpm_submit_cmd(locality, TPM_ORD_GET_RANDOM, in_size, &out_size);

#ifdef TPM_TRACE
    printf("TPM: get random %u bytes, return value = %08X\n", *data_size, ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: get random %u bytes, return value = %08X\n", *data_size,
               ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    if ( out_size <= sizeof(*data_size) ) {
        *data_size = 0;
        return ret;
    }

    out_size -= sizeof(*data_size);
    reverse_copy(data_size, WRAPPER_OUT_BUF, sizeof(*data_size));
    if ( *data_size > 0 )
        memcpy(random_data, WRAPPER_OUT_BUF + sizeof(*data_size), *data_size);

    /* data might be used as key, so clear from buffer memory */
    memset(WRAPPER_OUT_BUF + sizeof(*data_size), 0, *data_size);

    /* if TPM doesn't return all requested random bytes, try one more time */
    if ( *data_size < requested_size ) {
        printf("requested %x random bytes but only got %x\n", requested_size,
               *data_size);
        /* we're only going to try twice */
        if ( first_attempt ) {
            first_attempt = false;
            second_size = requested_size - *data_size;
            printf("trying one more time to get remaining %x bytes\n",
                   second_size);
            ret = tpm_get_random(locality, random_data + *data_size,
                                 &second_size);
            *data_size += second_size;
        }
    }

    return ret;
}

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */

