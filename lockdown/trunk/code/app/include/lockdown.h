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

// lockdown specific declarations/definitions
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __LOCKDOWN_H__
#define __LOCKDOWN_H__


//specific defines for VT BOX
//#define LDN_ENV_TRUSTED_STARTSECTOR  (63)
//#define LDN_ENV_TRUSTED_ENDSECTOR  (12578894)
//#define LDN_NULL_SECTOR  (300000000)
//#define LDN_IDE_BUS   0xC000
//#define LDN_ALLOWED_SECTORS 0xFFFFFFFFUL
//#define LDN_MACHINE_NETWORKDEVICES {1,0,0},{2,0,0}
//#define LDN_OUTOFBOUNDS_CHECK	(((u64)lbaaddr >= (u64)LDN_ENV_TRUSTED_STARTSECTOR) && ((u64)lbaaddr <= (u64)LDN_ENV_TRUSTED_ENDSECTOR)) || ((u64)lbaaddr < 63ULL) 

/*//hyper-partitioning configuration (specific to the platform/installation)
//hp6555b
#define LDN_ENV_TRUSTED_STARTSECTOR  	(159396993)
#define LDN_ENV_TRUSTED_ENDSECTOR  		(222291404)
#define LDN_NULL_SECTOR  				(620000000)
#define LDN_IDE_BUS   					0x6010
#define LDN_ALLOWED_SECTORS 			159396930
#define LDN_OUTOFBOUNDS_CHECK			(((u64)lbaaddr >= (u64)LDN_ENV_TRUSTED_STARTSECTOR) && ((u64)lbaaddr <= (u64)LDN_ENV_TRUSTED_ENDSECTOR)) || ((u64)lbaaddr < 63ULL) || ((u64)lbaaddr >= 63ULL && (u64)lbaaddr <= 33554494ULL)
*/


//hyper-partitioning configuration (specific to the platform/installation)
//hp8450p
#define LDN_ENV_TRUSTED_STARTSECTOR  	(159396993)
#define LDN_ENV_TRUSTED_ENDSECTOR  		(222291404)
#define LDN_NULL_SECTOR  				(620000000)
#define LDN_IDE_BUS   					0x1F0
#define LDN_ALLOWED_SECTORS 			33554495, 96470325, 159396991
#define LDN_OUTOFBOUNDS_CHECK			(((u64)lbaaddr >= (u64)LDN_ENV_TRUSTED_STARTSECTOR) && ((u64)lbaaddr <= (u64)LDN_ENV_TRUSTED_ENDSECTOR)) || ((u64)lbaaddr < 63ULL) || ((u64)lbaaddr >= 63ULL && (u64)lbaaddr <= 33554494ULL)


#define LDN_MACHINE_NETWORKDEVICES {0x44,0,0},{0x46,0x06,0x00}

extern u32 LDN_ENV_PHYSICALMEMORYLIMIT;

#ifndef __ASSEMBLY__

#define LDN_ENV_TRUSTED_SIGNATURE  0x45555254   //"TRUE"
#define LDN_ENV_UNTRUSTED_SIGNATURE 0x45544E55  //"UNTE"


typedef struct {
	u32 signature;  				//trusted or untrusted env. being switched to
	u32 full_hashlist_count;		//no. of full code page hashes
	u32 partial_hashlist_count;		//no. of partial code page hashes
									//full and partial hash list follow
									//20 bytes (160-bits) per entry
} __attribute__((packed)) LDNPB;


#endif //__ASSEMBLY__


#include <lockdown-acpi.h>
#include <lockdown-atapi.h>
#include <lockdown-exepe.h>
#include <hyperpart.h>
#include <approvedexec.h>


#endif //__LOCKDOWN_H__
