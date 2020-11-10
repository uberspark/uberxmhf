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

//Intel VT-d declarations/definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark.h>
#include <xmhfhw.h>




//vt-d register write function
/*@
	requires \valid(dmardevice);
	assigns \nothing;
@*/
void _vtd_reg_write(VTD_DRHD *dmardevice, uint32_t reg, uint64_t value){
  uint32_t regtype=VTD_REG_32BITS, regaddr=0;

	//obtain register type and base address
  switch(reg){
    //32-bit registers
    case  VTD_VER_REG_OFF:
    case  VTD_GCMD_REG_OFF:
    case  VTD_GSTS_REG_OFF:
    case  VTD_FSTS_REG_OFF:
    case  VTD_FECTL_REG_OFF:
    case  VTD_PMEN_REG_OFF:
    case  VTD_PLMBASE_REG_OFF:
    case  VTD_PLMLIMIT_REG_OFF:
      regtype=VTD_REG_32BITS;
      regaddr=dmardevice->regbaseaddr+reg;
      break;

    //64-bit registers
    case  VTD_CAP_REG_OFF:
    case  VTD_ECAP_REG_OFF:
    case  VTD_RTADDR_REG_OFF:
    case  VTD_CCMD_REG_OFF:
    case  VTD_PHMBASE_REG_OFF:
    case  VTD_PHMLIMIT_REG_OFF:
      regtype=VTD_REG_64BITS;
      regaddr=dmardevice->regbaseaddr+reg;
      break;

    case  VTD_IOTLB_REG_OFF:
      regtype=VTD_REG_64BITS;
      regaddr=dmardevice->iotlb_regaddr;
      break;


    case  VTD_IVA_REG_OFF:
      regtype=VTD_REG_64BITS;
      regaddr=dmardevice->iva_regaddr;
      break;


    default:
      //_XDPRINTF_("%s: Halt, Unsupported register=%08x\n", __func__, reg);
      break;
  }

  //perform the actual read or write request
	switch(regtype){
    case VTD_REG_32BITS:	//32-bit write
      CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu32, regaddr, (uint32_t)value);
      break;

    case VTD_REG_64BITS:	//64-bit write
      CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu64, regaddr, (uint32_t)value, (uint32_t)((uint64_t)value >> 32) );
      break;

    default:
     //_XDPRINTF_("%s: Halt, Unsupported access width=%08x\n", __func__, regtype);
     break;
  }

  return;
}



