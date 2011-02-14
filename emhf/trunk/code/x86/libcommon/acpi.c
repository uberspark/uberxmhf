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

//	acpi.c 
//  advanced configuration and power-management interface subsystem 
//	glue code
//  author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

//------------------------------------------------------------------------------
//TODO: move these into flat.c for unified FLAT memory accesses from both SL
//and runtime
//functions to read memory using flat selector to access ACPI related
//data structures below SL base
static u8 flat_readu8(u32 addr){
    u32 ret;
    __asm__ __volatile("xor %%eax, %%eax\r\n"        
                       "movl %%fs:(%%ebx), %%eax\r\n"
                       : "=a"(ret)
                       : "b"(addr)
                       );
    return (u8)ret;        
}


//memory copy using FLAT addresses, dest is always assumed to be DS relative
//(typically a variable) while src is assumed to be an absolute physical
//memory address
static void flat_copy(u8 *dest, u8 *src, u32 size){
	u32 i;
	u8 val;
	for(i=0; i < size; i++){
		val = flat_readu8((u32)src + i);
		dest[i] = val;
	}
}


//------------------------------------------------------------------------------
//compute checksum of ACPI table
static u32 _acpi_computetablechecksum(u32 spaddr, u32 size){
  char *p;
  char checksum=0;
  u32 i;

  p=(char *)spaddr;
  
  for(i=0; i< size; i++)
    checksum+= (char)(*(p+i));
  
  return (u32)checksum;
}


//------------------------------------------------------------------------------
//get the physical address of the root system description pointer (rsdp)
//return 0 in case of error (ACPI RSDP not found)
u32 acpi_getRSDP(ACPI_RSDP *rsdp){
  u16 ebdaseg;
  u32 ebdaphys;
  u32 i, found=0;
  
  //get EBDA segment from 040E:0000h in BIOS data area
  flat_copy((u8 *)&ebdaseg, (u8 *)0x0000040E, sizeof(u16));

  //convert it to its 32-bit physical address
  ebdaphys=(u32)(ebdaseg * 16);

  //search first 1KB of ebda for rsdp signature (8 bytes long)
  for(i=0; i < (1024-8); i+=16){
    flat_copy((u8 *)rsdp, (u8 *)(ebdaphys+i), sizeof(ACPI_RSDP));
    if(rsdp->signature == ACPI_RSDP_SIGNATURE){
      if(!_acpi_computetablechecksum((u32)rsdp, 20)){
        found=1;
        break;
      }
    }
  }

	//found RSDP?  
  if(found)
    return 1;
  
  //nope, search within BIOS areas 0xE0000 to 0xFFFFF
  for(i=0xE0000; i < (0xFFFFF-8); i+=16){
    flat_copy((u8 *)rsdp, (u8 *)i, sizeof(ACPI_RSDP));
    if(rsdp->signature == ACPI_RSDP_SIGNATURE){
      if(!_acpi_computetablechecksum((u32)rsdp, 20)){
        found=1;
        break;
      }
    }
  }

  //found RSDP?
  if(found)
    return 1;
  
  //no RSDP, system is not ACPI compliant!
  return 0;  
}
//------------------------------------------------------------------------------

