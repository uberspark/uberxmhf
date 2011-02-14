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

//vmx_eap.h - VMX VT-d (External Access Protection) declarations/definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __VMX_EAP_H__
#define __VMX_EAP_H__

#define VTD_DMAR_SIGNATURE  (0x52414D44) //"DMAR"
#define VTD_MAX_DRHD   8		//maximum number of DMAR h/w units   


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


//initialize VMX EAP a.k.a VT-d
//returns 1 if all went well, else 0
u32 vmx_eap_initialize(void);

#endif //__ASSEMBLY__

#endif //__VMX_EAP_H__