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

//vmx_eap.h - VMX VT-d (External Access Protection) declarations/definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __VMX_EAP_H__
#define __VMX_EAP_H__

#define VTD_DMAR_SIGNATURE  (0x52414D44) //"DMAR"
#define VTD_MAX_DRHD   8		//maximum number of DMAR h/w units   

//VT-d register offsets (sec. 10.4, Intel_VT_for_Direct_IO)
#define VTD_VER_REG_OFF 		0x000				//arch. version (32-bit)
#define VTD_CAP_REG_OFF 		0x008				//h/w capabilities (64-bit)				
#define VTD_ECAP_REG_OFF  	0x010				//h/w extended capabilities (64-bit)
#define VTD_GCMD_REG_OFF  	0x018				//global command (32-bit)
#define VTD_GSTS_REG_OFF  	0x01C				//global status (32-bit)
#define VTD_RTADDR_REG_OFF  0x020				//root-entry table address (64-bit)
#define VTD_CCMD_REG_OFF  	0x028				//manage context-entry cache (64-bit) 
#define VTD_FSTS_REG_OFF  	0x034				//report fault/error status (32-bit)
#define VTD_FECTL_REG_OFF 	0x038				//interrupt control (32-bit)
#define VTD_PMEN_REG_OFF  	0x064				//enable DMA protected memory regions (32-bits)
#define VTD_IVA_REG_OFF  		0x0DEAD  		//invalidate address register (64-bits)
																				//note: the offset of this register is computed
                                    		//at runtime for a specified DMAR device
#define VTD_IOTLB_REG_OFF   0x0BEEF     //IOTLB invalidate register (64-bits)
																				//note: the offset is VTD_IVA_REG_OFF + 8 and
																				//computed at runtime for a specified DMAR device


//VT-d register access types (custom definitions)
#define VTD_REG_READ  			0xaa				//read VTD register
#define VTD_REG_WRITE 			0xbb				//write VTD register

//Vt-d register access widths (custom definitions)
#define VTD_REG_32BITS  		0x32ff
#define VTD_REG_64BITS  		0x64ff

//Vt-d page-table bits
#define VTD_READ						0x1
#define VTD_WRITE						0x2
#define VTD_SUPERPAGE				(0x1UL << 7)


#ifndef __ASSEMBLY__

//Vt-d DMAR structure
typedef struct{
  u32 signature;
  u32 length;
  u8 revision;
  u8 checksum;
  u8 oemid[6];
  u64 oemtableid;
	u32 oemrevision;
	u32 creatorid;
	u32 creatorrevision;
  u8 hostaddresswidth;
  u8 flags;
  u8 rsvdz[10];    
}__attribute__ ((packed)) VTD_DMAR;

//VT-d DRHD structure
typedef struct{
  u16 type;
  u16 length;
  u8 flags;
  u8 rsvdz0;
  u16 pcisegment;
  u64 regbaseaddr;
}__attribute__ ((packed)) VTD_DRHD;


//------------------------------------------------------------------------------
//VT-d register structure definitions

//VTD_VER_REG (sec. 10.4.1)
typedef union {
  u32 value;
  struct
  {
    u32 min : 4;			//minor version no.
    u32 max : 4;			//major version no.
    u32 rsvdz : 24;		//reserved
  } bits;
} __attribute__ ((packed)) VTD_VER_REG;

//VTD_CAP_REG (sec. 10.4.2)
typedef union {
  u64 value;
  struct
  {
    u32 nd : 3;    		//no. of domains
    u32 afl : 1;			//advanced fault logging
    u32 rwbf : 1;			//required write-buffer flushing
    u32 plmr : 1;			//protected low-memory region
    u32 phmr : 1;			//protected high-memory region
    u32 cm : 1;				//caching mode
    u32 sagaw: 5;			//supported adjuested guest address widths
    u32 rsvdz0: 3;		//reserved
    u32 mgaw : 6;			//maximum guest address width
    u32 zlr: 1;				//zero length read
    u32 isoch: 1;			//isochrony
    u32 fro : 10;			//fault-recording register offset
    u32 sps : 4;			//super-page support
    u32 rsvdz1: 1;		//reserved
    u32 psi: 1;				//page selective invalidation
    u32 nfr: 8;				//no. of fault-recording registers
    u32 mamv: 6;			//max. address mask value
    u32 dwd: 1;				//DMA write draining
    u32 drd: 1;				//DMA read draining
    u32 rsvdz2: 8;		//reserved
  } bits;
} __attribute__ ((packed)) VTD_CAP_REG;

//VTD_ECAP_REG (sec. 10.4.3)
typedef union {
  u64 value;
  struct
  {
    u32 c:1;					//coherency
    u32 qi:1;					//queued invalidation support
    u32 di:1;					//device IOTLB support
    u32 ir:1;					//interrupt remapping support
    u32 eim:1;				//extended interrupt mode
    u32 ch:1;					//caching hints
    u32 pt:1;					//pass through 
    u32 sc:1;					//snoop control
    u32 iro:10;				//IOTLB register offset
    u32 rsvdz0: 2;		//reserved
    u32 mhmv: 4;			//maximum handle mask value
    u64 rsvdz1: 40;		//reserved
  } bits;
} __attribute__ ((packed)) VTD_ECAP_REG;

//VTD_GCMD_REG (sec. 10.4.4)
typedef union {
  u32 value;
  struct
  {
    u32 rsvdz0: 23;		//reserved
    u32 cfi: 1;				//compatibility format interrupt
    u32 sirtp: 1;			//set interrupt remap table pointer
    u32 ire:1;				//interrupt remapping enable
    u32 qie:1;				//queued invalidation enable
    u32 wbf:1;				//write buffer flush
    u32 eafl:1;				//enable advanced fault logging
    u32 sfl:1;				//set fault log
    u32 srtp:1;				//set root table pointer
    u32 te:1;					//translation enable
  } bits;
} __attribute__ ((packed)) VTD_GCMD_REG;

//VTD_GSTS_REG (sec. 10.4.5)
typedef union {
  u32 value;
  struct
  {
    u32 rsvdz0: 23;		//reserved
    u32 cfis:1;				//compatibility interrupt format status
    u32 irtps:1;			//interrupt remapping table pointer status
    u32 ires:1;				//interrupt remapping enable status
    u32 qies:1;				//queued invalidation enable status
    u32 wbfs:1;				//write buffer flush status
    u32 afls:1;				//advanced fault logging status
    u32 fls:1;				//fault log status
    u32 rtps:1;				//root table pointer status
    u32 tes:1;				//translation enable status 
  } bits;
} __attribute__ ((packed)) VTD_GSTS_REG;

//VTD_RTADDR_REG (sec. 10.4.6)
typedef union {
  u64 value;
  struct
  {
    u32 rsvdz0: 12;		//reserved
    u64 rta: 52;			//root table address
  } bits;
} __attribute__ ((packed)) VTD_RTADDR_REG;

//VTD_CCMD_REG (sec. 10.4.7)
typedef union {
  u64 value;
  struct
  {
    u32 did:16;				//domain id
    u32 sid:16;				//source id
    u32 fm:2;					//function mask
    u32 rsvdz0: 25;		//reserved
    u32 caig:2;				//context invalidation actual granularity
    u32 cirg:2;				//context invalidation request granularity
    u32 icc:1;				//invalidate context-cache 
  } bits;
} __attribute__ ((packed)) VTD_CCMD_REG;

//VTD_IOTLB_REG (sec. 10.4.8.1)
typedef union {
  u64 value;
  struct
  {
    u32 rsvdz0: 32;		//reserved
    u32 did:16;				//domain-id
    u32 dw: 1;				//drain writes
    u32 dr:1;					//drain reads
    u32 rsvdz1: 7;		//reserved
    u32 iaig: 3;			//IOTLB actual invalidation granularity
    u32 iirg: 3;			//IOTLB request invalidation granularity
    u32 ivt: 1;				//invalidate IOTLB 
  } bits;
} __attribute__ ((packed)) VTD_IOTLB_REG;

//VTD_IVA_REG (sec. 10.4.8.2)
typedef union {
  u64 value;
  struct
  {
    u32 am: 6;				//address mask
    u32 ih:1;					//invalidation hint
    u32 rsvdz0: 5;		//reserved
    u64 addr:52;			//address
  } bits;
} __attribute__ ((packed)) VTD_IVA_REG;


//VTD_FSTS_REG	(sec. 10.4.9)
typedef union {
  u32 value;
  struct
  {
    u32 pfo:1;				//fault overflow
    u32 ppf:1;				//primary pending fault
    u32 afo:1;				//advanced fault overflow
    u32 apf:1;				//advanced pending fault
    u32 iqe:1;				//invalidation queue error				
    u32 ice:1;				//invalidation completion error
    u32 ite:1;				//invalidation time-out error
    u32 rsvdz0: 1;		//reserved
    u32 fri:8;				//fault record index
    u32 rsvdz1: 16;		//reserved
  } bits;
} __attribute__ ((packed)) VTD_FSTS_REG;

//VTD_FECTL_REG	(sec. 10.4.10)
typedef union {
  u32 value;
  struct
  {
    u32 rsvdp0:30;		//reserved
    u32 ip:1;					//interrupt pending
    u32 im:1;					//interrupt mask
  } bits;
} __attribute__ ((packed)) VTD_FECTL_REG;

//VTD_PMEN_REG (sec. 10.4.16)
typedef union {
  u32 value;
  struct
  {
    u32 prs:1;			//protected region status
    u32 rsvdp:30;		//reserved
    u32 epm:1;			//enable protected memory
  } bits;
} __attribute__ ((packed)) VTD_PMEN_REG;

		
#endif //__ASSEMBLY__

#endif //__VMX_EAP_H__
