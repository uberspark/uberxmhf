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


#include <lockdown/types.h>
#include <lockdown/print.h>
#include <lockdown/lockdown.h>
#include <lockdown/msr.h>
#include <lockdown/processor.h>
#include <lockdown/svm.h>
#include <lockdown/paging.h>
#include <lockdown/io.h>
#include <lockdown/pci.h>

#include <tpm/tpm.h>


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

    slb_out_info("buffer for slb_tis_transmit:"); 
    slb_dump_bytes(buffer, 34); 
    
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

    *value = -1;

    send_buffer[0] = TPM_ORD_GetCapability; /* ordinal    0x65 */
    send_buffer[1] = TPM_CAP_PROPERTY;      /* capArea    0x 5 */
    send_buffer[2] = TPM_SUBCAP;            /* subCapSize 0x 4 */
    send_buffer[3] = subcap;                /* subCap */
    
    buffer[0] = 0x00;
    buffer[1] = 0xc1;
    size+=sizeof(send_buffer); /* 6 + 16 */
    *(unsigned long *)(buffer+2) = slb_ntohl(size);
    slb_assert(TCG_BUFFER_SIZE>=size);
    for (i=0; i<sizeof(send_buffer)/sizeof(*send_buffer); i++)	{
        *((unsigned long *)(buffer+6)+i) = slb_ntohl(send_buffer[i]);
    }
/*     slb_out_info("buffer for slb_tis_transmit:");     */
/*     slb_dump_bytes(buffer, size); */
    ret = slb_tis_transmit(buffer, size, TCG_BUFFER_SIZE,TIS_LOCALITY_3);
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
    *(unsigned long *)(buffer+2) = slb_ntohl(size);				
    slb_assert(TCG_BUFFER_SIZE>=size);					
    for (i=0; i<sizeof(send_buffer)/sizeof(*send_buffer); i++)	{
        *((unsigned long *)(buffer+6)+i) = slb_ntohl(send_buffer[i]);		
    } 
    ret = slb_tis_transmit(buffer, size, TCG_BUFFER_SIZE, TIS_LOCALITY_3);
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
    *((unsigned long *)(buffer+2)) = slb_ntohl(size); 
    slb_assert(TCG_BUFFER_SIZE>=size);					
    for (i=0; i<sizeof(send_buffer)/sizeof(*send_buffer); i++)	{
        *((unsigned long *)(buffer+6)+i) = slb_ntohl(send_buffer[i]);		
    } 
    /* the 14 is tag(2),paramSize(4),returnCode(4),randomBytesSize(4) */
    ret = slb_tis_transmit(buffer, size, bytesRequested+14, TIS_LOCALITY_3);
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
