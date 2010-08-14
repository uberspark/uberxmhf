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
 * \brief   TPM commands compiled with the TCG TPM Spec v1.2.
 * \date    2006-03-28
 * \author  Bernhard Kauer <kauer@tudos.org>
 */
/*
 * Copyright (C) 2006  Bernhard Kauer <kauer@tudos.org>
 * Technische Universitaet Dresden, Operating Systems Research Group
 *
 * This file is part of the OSLO package, which is distributed under
 * the  terms  of the  GNU General Public Licence 2.  Please see the
 * COPYING file for details.
 */
/**
 * Modified by Jonathan M. McCune for use with Flicker in 2007.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2.0 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#include <types.h>
#include <error.h>
#include <multiboot.h>
#include <string.h>
#include <print.h>
#include <svm.h>
#include <sha1.h>
#include <processor.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <io.h>
#include <pci.h>
#include <dev.h>
#include <tpm.h>


unsigned short slb_ntohs(unsigned short in) {
    unsigned short out;
    unsigned char* inp;
    unsigned char* outp;
    
    inp = (unsigned char *)&in;
    outp = (unsigned char *)&out;

    outp[0] = inp[1];
    outp[1] = inp[0];
    
    return out;
}

unsigned long slb_ntohl(unsigned long in) {
    unsigned char *s = (unsigned char *)&in;
    return (unsigned long)(s[0] << 24 | s[1] << 16 | s[2] << 8 | s[3]);
}

/**
 * Extend a PCR with a hash.
 */
int
slb_TPM_Extend(unsigned char *buffer,
               unsigned long pcrindex, unsigned char *hash)
{
    int res;
    
    ((unsigned int *)buffer)[0] = 0x0000c100;
    ((unsigned int *)buffer)[1] = 0x00002200; /* length = 34 */
    ((unsigned int *)buffer)[2] = 0x00001400;
    *((unsigned int *) (buffer+10))=slb_ntohl(pcrindex);

    TPM_COPY_TO(hash, 4, TCG_HASH_SIZE);

    slb_out_info("TPM_Extend buffer for slb_tis_transmit:"); 
    dump_bytes(buffer, 34); 
    
    res = slb_tis_transmit(buffer, 34, TCG_BUFFER_SIZE, TIS_LOCALITY_3);
    TPM_COPY_FROM(hash, 0, TCG_HASH_SIZE);
    slb_out_description("TPM Extend: res", res);
    return res < 0 ? res : (int) slb_ntohl(*((unsigned int *) (buffer+6)));
}


int TPM_GetSubCap (unsigned char *buffer, unsigned int *value,
                  unsigned long subcap) {
    unsigned i; 
    int ret;								
    int size = 6; /* tag + paramSize */
    unsigned long send_buffer[4];

/*     slb_out_info("entering TPM_GetSubCap"); */

    if(!value) { return -1; }

    *value = (unsigned int)-1;

    send_buffer[0] = TPM_ORD_GetCapability; /* ordinal    0x65 */
    send_buffer[1] = TPM_CAP_PROPERTY;      /* capArea    0x 5 */
    send_buffer[2] = TPM_SUBCAP;            /* subCapSize 0x 4 */
    send_buffer[3] = subcap;                /* subCap */
    
    buffer[0] = 0x00;
    buffer[1] = 0xc1;
    size+=sizeof(send_buffer); /* 6 + 16 */
    *(unsigned long *)(buffer+2) = slb_ntohl((unsigned long)size);
    slb_assert(TCG_BUFFER_SIZE>=size);
    for (i=0; i<sizeof(send_buffer)/sizeof(*send_buffer); i++)	{
        *((unsigned long *)(buffer+6)+i) = slb_ntohl(send_buffer[i]);
    }
/*     slb_out_info("buffer for slb_tis_transmit:");     */
/*     dump_bytes(buffer, size); */
    ret = slb_tis_transmit(buffer, (unsigned int)size, TCG_BUFFER_SIZE,TIS_LOCALITY_3);
    if (ret < 0) {
/*         slb_out_description("slb_tis_transmit returned error: ", ret); */
        return ret;
    }
    if (TPM_EXTRACT_LONG(0)!=4) {
/*         slb_out_description("TPM_EXTRACT_LONG(0) should be 4, instead it's: ", TPM_EXTRACT_LONG(0)); */
        return -2;
    }
    *value=TPM_EXTRACT_LONG(4);
    return slb_ntohl(*(unsigned long *)(buffer+6));			        
}


/**
 * Read a pcr value.
 * Returns the value of the pcr in pcrvalue.
 */
int slb_TPM_PcrRead(unsigned char *buffer, unsigned long index,
                    unsigned char *value)  {						
    unsigned i; 
    int ret;								
    int size = 6;							
    unsigned long send_buffer[2];

    send_buffer[0] = TPM_ORD_PcrRead;
    send_buffer[1] = index;

    if (value==0) return -1;

    buffer[0] = 0x00;							
    buffer[1] = 0xc1;							
    size+=sizeof(send_buffer);						
    *(unsigned long *)(buffer+2) = slb_ntohl((unsigned long)size);
    slb_assert(TCG_BUFFER_SIZE>=size);					
    for (i=0; i<sizeof(send_buffer)/sizeof(*send_buffer); i++)	{
        *((unsigned long *)(buffer+6)+i) = slb_ntohl(send_buffer[i]);		
    } 
    ret = slb_tis_transmit(buffer, (unsigned int)size, TCG_BUFFER_SIZE, TIS_LOCALITY_3);
    if (ret < 0)							
        return ret;							

    TPM_COPY_FROM(value, 0, TCG_HASH_SIZE);
    return slb_ntohl(*(unsigned long *)(buffer+6));			        
}

/**
 * Get numBytes random bytes from the TPM.  bytes is assumed to point
 * to a region of memory big enough to contain numBytes bytes.  Return
 * value is number of bytes actually written, or 0 if error.
 */
int TPM_GetRandom(unsigned char *buffer, unsigned int bytesRequested,
                  unsigned char *bytes) {
    unsigned int i; 
    int ret;								
    int size = 6; /* tag + paramSize */
    unsigned long send_buffer[2];
    unsigned int randomBytesSize;

    send_buffer[0] = TPM_ORD_GetRandom;
    send_buffer[1] = bytesRequested;

    if (bytes==0) return -1;

    buffer[0] = 0x00;
    buffer[1] = 0xc1;
    size+=sizeof(send_buffer);						
    *((unsigned long *)(buffer+2)) = slb_ntohl((unsigned long)size); 
    slb_assert(TCG_BUFFER_SIZE>=size);					
    for (i=0; i<sizeof(send_buffer)/sizeof(*send_buffer); i++)	{
        *((unsigned long *)(buffer+6)+i) = slb_ntohl(send_buffer[i]);		
    } 
    /* the 14 is tag(2),paramSize(4),returnCode(4),randomBytesSize(4) */
    ret = slb_tis_transmit(buffer, (unsigned int)size, bytesRequested+14, TIS_LOCALITY_3);
    //    slb_out_description("slb_tis_transmit returned:", ret);

    if (ret < 0)    
        return ret;

    ret = *((int *)(buffer+6));
    //    slb_out_description("TPM returnCode:", ret);

    randomBytesSize = *((unsigned int *)(buffer+10));    
    //    slb_out_description("TPM returned bytes: ", randomBytesSize);

    for(i=0; i<randomBytesSize && i<bytesRequested; i++) {
        bytes[i] = buffer[14+i];
    }

    return i;
}



void slb_print_tpm_error(int error) {
    if(TPM_INVALID_AUTHHANDLE == error) {
        slb_out_description("ERROR: TPM_INVALID_AUTHHANDLE", error);
    } else if(TPM_AUTHFAIL == error) {
        slb_out_description("ERROR: TPM_AUTHFAIL", error);
    } else if(TPM_BAD_DATASIZE == error) {
        slb_out_description("ERROR: TPM_BAD_DATASIZE", error);
    } else if(TPM_ENCRYPT_ERROR == error) {
        slb_out_description("ERROR: TPM_ENCRYPT_ERROR", error);
    } else if(TPM_DECRYPT_ERROR == error) {
        slb_out_description("ERROR: TPM_DECRYPT_ERROR", error);
    } else if(TPM_BAD_PARAMETER == error) {
        slb_out_description("ERROR: TPM_BAD_PARAMETER", error);
    } else if(TPM_RESOURCES == error) {
        slb_out_description("ERROR: TPM_RESOURCES", error);
    } else if(TPM_BAD_COUNTER == error) {
        slb_out_description("ERROR: TPM_BAD_COUNTER", error);
    } else if(TPM_NON_FATAL == error) {
        slb_out_description("ERROR: TPM_NON_FATAL (TPM_RETRY)", error);
    } else {
        slb_out_description("ERROR: UNKNOWN", error);
    }            
}
