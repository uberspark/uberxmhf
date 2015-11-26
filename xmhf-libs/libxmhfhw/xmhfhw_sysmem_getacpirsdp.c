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

// Platform BIOS data structure access
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>


//------------------------------------------------------------------------------
//compute checksum of ACPI table
/*@
	requires size >= 0;
	requires \valid((char *)table+(0..size-1));
	assigns \nothing;
@*/
static u32 _acpi_computetablechecksum(char *table, u32 size){
  char *p;
  char checksum=0;
  u32 i;

  p=(char *)table;

	/*@
		loop invariant I1: 0 <= i <= size;
		loop assigns i, checksum;
		loop variant size - i;
	@*/

	for(i=0; i< size; i++)
	  checksum+= (char)(*(p+i));

  return (u32)checksum;
}




//*
//------------------------------------------------------------------------------
//get the physical address of the root system description pointer (rsdp)
//return 0 in case of error (ACPI RSDP not found) else the absolute physical
//memory address of the RSDP
/*@
	requires \valid(rsdp);
	assigns \nothing;
@*/
u32 xmhfhw_platform_x86pc_acpi_getRSDP(ACPI_RSDP *rsdp){
  u16 ebdaseg;
  u32 ebdaphys;
  u32 i, found=0;


  //get EBDA segment from 040E:0000h in BIOS data area
  //xmhfhw_sysmemaccess_copy((u8 *)&ebdaseg, (u8 *)0x0000040E, sizeof(u16));
  ebdaseg = CASM_FUNCCALL(xmhfhw_sysmemaccess_readu16, 0x0000040EUL);

  //convert it to its 32-bit physical address
  ebdaphys=(u32)(ebdaseg * 16);
  _XDPRINTF_("%s:%u ebdaseg=%x, ebdaphys=%x\n", __func__, __LINE__,
	(u32)ebdaseg, ebdaphys);

  //@assert 1;

  //search first 1KB of ebda for rsdp signature (8 bytes long)
	/*@
		loop invariant I2: 0 <= i <= 1040;
		loop assigns i, found;
		loop variant (1024-8) - i;
	@*/

  for(i=0; i < (1024-8); i+=16){
    CASM_FUNCCALL(xmhfhw_sysmem_copy_sys2obj, (u8 *)rsdp, (u8 *)(ebdaphys+i), sizeof(ACPI_RSDP));
    if(rsdp->signature == ACPI_RSDP_SIGNATURE){
      if(!_acpi_computetablechecksum((char *)rsdp, 20)){
        found=1;
        break;
      }
    }
  }


  //@assert 1;
	//found RSDP?
  if(found)
    return (u32)(ebdaphys+i);

  //@assert 1;


  //nope, search within BIOS areas 0xE0000 to 0xFFFFF
	/*@
		loop invariant I3: 0xE0000 <= i <= (0xFFFFF+16);
		loop assigns i, found;
		loop variant (0xFFFFF-8) - i;
	@*/
  for(i=0xE0000; i < (0xFFFFF-8); i+=16){
    CASM_FUNCCALL(xmhfhw_sysmem_copy_sys2obj, (u8 *)rsdp, (u8 *)i, sizeof(ACPI_RSDP));
    if(rsdp->signature == ACPI_RSDP_SIGNATURE){
      //@assert 1;
      if(!_acpi_computetablechecksum((char *)rsdp, 20)){
        found=1;
        break;
      }
    }
  }


  //found RSDP?
  if(found)
    return i;

  //@assert 1;

  //no RSDP, system is not ACPI compliant!
  return 0;
}
//------------------------------------------------------------------------------
