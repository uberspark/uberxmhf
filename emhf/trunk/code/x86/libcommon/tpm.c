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
 *
 * "Extra" functions unnecessary in SL denoted as such.
 */

#include <target.h>
#include <tpm.h>




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



static tpm_timeout_t g_timeout = {TIMEOUT_A,
                                  TIMEOUT_B,
                                  TIMEOUT_C,
                                  TIMEOUT_D};

void dump_locality_access_regs(void) {
    tpm_reg_access_t reg_acc;
    uint32_t locality;

    printf("\n%s():\n", __FUNCTION__);
    for(locality=0; locality <= 3; locality++) {    
        read_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
        printf("  TPM: Locality %d Access reg content: 0x%02x\n",
               locality, (uint32_t)reg_acc._raw[0]);
        if ( reg_acc.tpm_reg_valid_sts == 0 ) {
            printf("    TPM: Access reg not valid\n");
        }
    }
}

void deactivate_all_localities(void) {
    tpm_reg_access_t reg_acc;
    uint32_t locality;

    printf("\nTPM: %s()\n", __FUNCTION__);
    for(locality=0; locality <= 3; locality++) {    
        reg_acc._raw[0] = 0;
        reg_acc.active_locality = 1;
        write_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
    }
}

uint32_t tpm_wait_cmd_ready(uint32_t locality)
{
    uint32_t            i;
    tpm_reg_access_t    reg_acc;
    tpm_reg_sts_t       reg_sts;

/*     //temporary debug prints */
/*     dump_locality_access_regs(); */
/*     deactivate_all_localities(); */
/*     dump_locality_access_regs(); */

    /* ensure the contents of the ACCESS register are valid */
    read_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
#ifdef TPM_TRACE
    printf("\nTPM: Access reg content: 0x%02x\n", (uint32_t)reg_acc._raw[0]);
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
        printf("TPM: access reg request use timeout (i=%d)\n", i);
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
/* static */
uint8_t     cmd_buf[TPM_CMD_SIZE_MAX];
/* static */
uint8_t     rsp_buf[TPM_RSP_SIZE_MAX];

/* static */
uint32_t _tpm_submit_cmd(uint32_t locality, uint16_t tag, uint32_t cmd,
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

/*static inline*/
uint32_t tpm_submit_cmd(uint32_t locality, uint32_t cmd,
                                      uint32_t arg_size, uint32_t *out_size)
{
   return  _tpm_submit_cmd(locality, TPM_TAG_RQU_COMMAND, cmd,
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



/* static */
uint32_t tpm_get_capability(
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


/* misc utility functions; probably belong elsewhere */
void hashandprint(const char* prefix, const u8 *bytes, size_t len) {
    SHA_CTX ctx;
    u8 digest[SHA_DIGEST_LENGTH];
    u64 start, end;

    printf("\nhashandprint: processing 0x%08x bytes at addr 0x%08x", len, (u32)bytes);
    
    start = rdtsc64();
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    SHA1_Init(&ctx);
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    SHA1_Update(&ctx, bytes, len);
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    SHA1_Final(digest, &ctx);
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    end = rdtsc64();
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    print_hex(prefix, digest, SHA_DIGEST_LENGTH);
    printf("\n[PERF] hashandprint: elapsed CPU cycles 0x%016llx", end-start);    

    /* Simulate PCR 17 value on AMD processor */
    if(len == 0x10000) {
        u8 zeros[SHA_DIGEST_LENGTH];
        u8 pcr17[SHA_DIGEST_LENGTH];
        memset(zeros, 0, SHA_DIGEST_LENGTH);
        
        SHA1_Init(&ctx);
        SHA1_Update(&ctx, zeros, SHA_DIGEST_LENGTH);
        SHA1_Update(&ctx, digest, SHA_DIGEST_LENGTH);
        SHA1_Final(pcr17, &ctx);

        print_hex("[AMD] Expected PCR-17: ", pcr17, SHA_DIGEST_LENGTH);
    }    
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

