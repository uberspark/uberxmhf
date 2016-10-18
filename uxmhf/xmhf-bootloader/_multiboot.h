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

// multiboot.h - declarations for the multiboot spec
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __MULTIBOOT_H_
#define __MULTIBOOT_H_

#define MULTIBOOT_HEADER_MAGIC 0x1badb002
#define MEM_INFO 0x01
#define MULTIBOOT_HEADER_FLAGS ((1<<ALIGNED)|(1<<MEM_INFO))
#define MULTIBOOT_BOOTLOADER_MAGIC 0x2badb002

// multiboot info structure flags 
#define MBI_MEMLIMITS  0x00
#define MBI_DRIVES     0x01
#define MBI_CMDLINE    0x02
#define MBI_MODULES    0x03
#define MBI_MEMMAP     0x06

#ifndef __ASSEMBLY__
// section header table for ELF 
typedef struct{
  u32 num;
  u32 size;
  u32 addr;
  u32 shndx;
}__attribute__((packed)) elf_section_header_table_t;

// multiboot information struct 
typedef struct{
  u32 flags;
  u32 mem_lower;
  u32 mem_upper;
  u32 boot_device;
  u32 cmdline;
  u32 mods_count;
  u32 mods_addr;
  elf_section_header_table_t elf_sec;
  u32 mmap_length;
  u32 mmap_addr;
}__attribute__((packed)) multiboot_info_t;

// The module structure. 
typedef struct {
  u32 mod_start;
  u32 mod_end;
  u32 string;
  u32 reserved;
}__attribute__((packed)) module_t;

// The memory map structure
typedef struct {
  u32 size;
  u32 base_addr_low;
  u32 base_addr_high;
  u32 length_low;
  u32 length_high;
  u32 type;
}__attribute__((packed)) memory_map_t;
#endif /*__ASSEMBLY*/

#endif /* __MULTIBOOT_H */
