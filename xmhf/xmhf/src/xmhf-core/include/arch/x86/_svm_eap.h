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

//svm_eap.h - SVM External Access Protection declarations/definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __SVM_EAP_H__
#define __SVM_EAP_H__

//DEV is part of the Miscellaneous Configuration HT Device that is
//guaranteed to be on bus 0, device 0x18 and function 3 (2.11 & 3.6, AMD BKDG)
//XXX: what is not clear from the doc. is whether there could be multiple DEV
//devices like on Intel platforms (VT-d DMAR).
#define	DEV_PCI_BUS				0x0
#define DEV_PCI_DEVICE		0x18
#define DEV_PCI_FUNCTION	0x3


//DEV function codes (15.24.5, AMD Dev. vol-2)
#define DEV_BASE_LO     	0
#define DEV_BASE_HI     	1
#define DEV_MAP         	2
#define DEV_CAP         	3
#define DEV_CR          	4
#define DEV_ERR_STATUS  	5
#define DEV_ERR_ADDR_LO 	6
#define DEV_ERR_ADDR_HI 	7


#ifndef __ASSEMBLY__

//SVM EAP container structure
struct _svm_eap {
	u32 dev_hdr_reg;			//DEV header register (32-bit)
 	u32 dev_fnidx_reg;		//DEV function/index register (32-bit)
	u32 dev_data_reg;			//DEV data register (32-bit)
	u32 dev_bitmap_vaddr;	//DEV bitmap virtual address
};


//DEV DEV_BASE_LO structure (p. 329, AMD BKDG)
typedef union dev_base_lo {
	u32 bytes;
  struct{
    u32 valid:1; 			//1= DEV enabled, 0= DEV disabled
    u32 protect:1; 		//0= allow out-of-range addresses, 1= disallow out-of-range addresses
    u32 size:5; 			//size of memory region that DEV covers (4GB*(2^size))
    u32 resv:5; 			//reserved
    u32 base_addr:20; //bits 12-31 of physical address of DEV table
  }fields;
} __attribute__ ((packed)) dev_base_lo_t;

//DEV DEV_BASE_HI structure (p. 330, AMD BKDG)
typedef union dev_base_hi {
  u32 bytes;
  struct{
    u32 base_addr:16; //bits 32-47 of physical address of DEV table
    u32 resv:16; 			//reserved
  }fields;
} __attribute__ ((packed)) dev_base_hi_t;

//DEV DEV_MAP structure (p. 330, AMD BKDG)
typedef union dev_map{
  u32 bytes;
  struct{
    u32 unit0:5; 	//I/O link unit 0 ID
    u32 valid0:1; //1= enable DEV for unit 0 and dom 0
    u32 unit1:5; 	//I/O link unit 1 ID
    u32 valid1:1; //1= enable DEV for unit 1 and dom 1
    u32 busno:8; 	//HT bus number
    u32 dom0:6; 	//protection domain number assigned to unit 0
    u32 dom1:6;		//protection domain number assigned to unit 1 
  }fields;
} __attribute__ ((packed)) dev_map_t;

//DEV DEV_CAP structure (p. 330, AMD BKDG)
typedef union dev_cap{
  u32 bytes;
  struct{
    u32 rev:8; 		//DEV register set revision number (00h for current)
    u32 n_doms:8; 	//number of protection domains implemented
    u32 n_maps:8; //number of map registers implemented
    u32 resv:8; 	//reserved
  }fields;
} __attribute__ ((packed)) dev_cap_t;

//DEV DEV_CR structure (p. 331, AMD BKDG)
typedef union dev_cr {
  u32 bytes;
  struct{
    u32 deven:1; 		//1=enable DEV
    u32 resv0:1;			//reserved
    u32 iodis:1; 		//1=disable upstream i/o cycles, set to 1 after SKINIT
    u32 mceen:1; 		//1=enable logging and reporting of DEV violations through MCE
    u32 devinv:1; 	//1=invalidate DEV table walk cache. bit cleared by h/w when complete
    u32 sldev:1; 		//1=memory region associated with SKINIT is internally protected, 0=use DEV table instead
    u32 walkprobe:1;//1=disable probing of CPU caches during DEV table walks
    u32 resv1:25; 		//bits 7-31 reserved 
  }fields;
} __attribute__ ((packed)) dev_cr_t;


//DEV DEV_ERR_STATUS structure (p	331 & 332, AMD BKDG)
typedef union dev_err_status {
	u32 bytes;
	struct{
		u32 accesstype:2;	//error code access type
#define	DEV_ERR_STATUS_ACCESSTYPE_GENERIC						0
#define	DEV_ERR_STATUS_ACCESSTYPE_READ              1
#define DEV_ERR_STATUS_ACCESSTYPE_WRITE             2
#define DEV_ERR_STATUS_ACCESSTYPE_READMODIFYWRITE		3		
		u32 source:3;		//error code source
#define DEV_ERR_STATUS_SOURCE_GENERIC								0
#define DEV_ERR_STATUS_SOURCE_CPU                   1
#define DEV_ERR_STATUS_SOURCE_DEVICE                2
		u32 dest:3;			//error code destination
#define DEV_ERR_STATUS_DEST_GENERIC									0
#define DEV_ERR_STATUS_DEST_DRAM                    1
#define DEV_ERR_STATUS_DEST_MMIO                    2
#define DEV_ERR_STATUS_DEST_IO                      4
#define DEV_ERR_STATUS_DEST_CONFIGURATION           5
		u32 resv0:8;			//reserved
		u32 mserror:8;		//model-specific error
		u32 resv1:5;			//reserved
		u32 addrvalid:1;	//error address valid
		u32 overflow:1;		//error overflow, 1=DEV violation was detected
		u32 valid:1;			//error valid, 1=DEV violation has been logged
	}fields;
} __attribute__ ((packed)) dev_err_status_t;


//DEV DEV_ERROR_ADDR_LO structure (p. 332, AMD BKDG)
typedef union dev_err_addr_lo {
	u32 bytes;
	struct{
		u32 resv0:2;	//reserved
		u32 addr:30;	//bits 2:31 of error address	
	}fields;
} __attribute__((packed)) dev_err_addr_lo_t;

//DEV DEV_ERROR_ADDR_HI structure (p. 332, AMD BKDG)
typedef union dev_err_addr_hi {
	u32 bytes;
	struct{
		u32 addr:16;	//bits 32-47 of error address
		u32 resv:16;	//reserved	
	}fields;
} __attribute__((packed)) dev_err_addr_hi_t;


#endif //__ASSEMBLY__

#endif	//__SVM_EAP_H__
