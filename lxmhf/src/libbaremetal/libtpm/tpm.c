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
 * Modified for XMHF by jonmccune@cmu.edu, 2011.01.18
 *
 * "Extra" functions unnecessary in SL denoted as such.
 */
 
/**
 * Adapted for libtpm - generic TPM library 
 * by Amit Vasudevan amitvasudevan@acm.org 
 */
 
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include <print_hex.h>
#include <tpm.h>


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

/* from emhf's processor.h */
static inline uint64_t rdtsc64(void)
{
  uint64_t rv;

  __asm__ __volatile__ ("rdtsc" : "=A" (rv));
  return (rv);
}

/*static inline*/
uint32_t tpm_submit_cmd(uint32_t locality, uint32_t cmd,
                                      uint32_t arg_size, uint32_t *out_size)
{
    uint32_t rv;
    uint64_t start, end;

    start = rdtsc64();
    rv = _tpm_submit_cmd(locality, TPM_TAG_RQU_COMMAND, cmd,
                         arg_size, out_size);
    end = rdtsc64();
    printf("TPM: PERF: Command 0x%08x consumed %lld cycles\n", cmd, end-start);
    return rv;
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
