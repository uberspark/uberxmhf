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

/* relocate.c code to relocate the TrustVisor and Linux kernel loaded 
 * by grub to locations required by version 2.04 (or higher) of the 
 * Linux/i386 boot protocol.
 * Written for TrustVisor by Ning Qu and Arvind Seshadri
 */

#include <types.h>
#include <error.h>
#include <multiboot.h>
#include <string.h>
#include <relocate.h>
#include <print.h>
#include <svm.h>
#include <visor.h>
#include <paging.h>
#include <msr.h>
#include <processor.h>
#include <e820.h>
#include <loader.h>
#include <sha1.h>
#include <ucode.h> /* for putbytes */

#define PUT_INIT_PARAMS(index, value)\
  ((*(u32 *)((u32)VISOR_LOAD_START + SKINIT_SLB_SIZE - 4 * (index))) = value)

#define GZIP_MAGIC 0x1f8b0800 /* gzip'd */  
#define INITRD_MAGIC 0x37303730

extern void realmode_start(void);
extern void realmode_end(void);
u32 relocate_kernel(module_t *mod_array, u32 mods_count);
u32 relocate_ucode(module_t *mod_array, u32 mods_count);

void relocate(multiboot_info_t *mbt)
{
  u32 max_pfn;
  u32 visor_size, visor_relocate_addr;
  module_t *mod_array = (module_t*)mbt->mods_addr;
  u32 mods_count = mbt->mods_count;
  u16 slb_length, slb_entry;

  u32 ucode_addr;
  
  sha1_context ctx;
  u8 visor_init_hash[SHA1_CHECKSUM_LEN];
  u8 tmp_hash[SHA1_CHECKSUM_LEN];
  u32 i;

  init_uart(); // XXX Put this some place more appropriate -Jon
  
  /* check if BIOS e820 map is available in the mmap_* fields of mbt */
  if ( !(mbt->flags & (1 << MBI_MEMMAP)) ){
    EARLY_FAIL();
  }

  /* process e820 map from grub */
  max_pfn = fix_e820(mbt);

  /* Relocate microcode patch (if present) */
  ucode_addr = relocate_ucode(mod_array, mods_count);
  
  /* relocate Linux kernel and initrd */ 
  if ( relocate_kernel(mod_array, mods_count) ){
    EARLY_FAIL();
  }

  /* relocate TrustVisor */
  visor_relocate_addr = (u32)VISOR_LOAD_START;
  visor_size = mod_array[0].mod_end - mod_array[0].mod_start;   
  if(visor_size > VISOR_INIT_SIZE + VISOR_RUNTIME_SIZE)
    EARLY_FAIL();
  memcpy((void*)visor_relocate_addr, (void*)mod_array[0].mod_start, 
         visor_size);
/*   putstr("visor_size (watch out for endianness): "); */
/*   putbytes((u8*)&visor_size, sizeof(u32)); */

  /* Calculate for outselves the SLB's entry point and length */
  slb_entry  = ((u16*)visor_relocate_addr)[0];
  slb_length = ((u16*)visor_relocate_addr)[1];

/*   putstr("slb_entry, slb_length (watch out for endianness):\n"); */
/*   putbytes((u8*)&slb_entry, sizeof(u16)); */
/*   putbytes((u8*)&slb_length, sizeof(u16)); */

  /* save the max_pfn for TrustVisor 
   * we can only do it right after relocating the TrustVisor 
   */
  PUT_INIT_PARAMS(1, max_pfn);
/*   putstr("max_pfn: "); */
/*   putbytes((u8*)&max_pfn, sizeof(u32)); */
  PUT_INIT_PARAMS(2, ucode_addr);
  
  /* move 16 bit real-mode code to fixed address */
  memcpy((void *)LOADER_REAL_START, &realmode_start, 
	 (u32)&realmode_end - (u32)&realmode_start);
  
  /**
   * Calculate the hash of the TrustVisor init section.
   * XXX Do we need to worry about the REAL mode code? -Jon
   */
  for(i=0; i<SHA1_CHECKSUM_LEN; i++) tmp_hash[i] = 0;
/*   putstr("First test SHA1 by hashing 20 bytes of 0s\n"); */
/*   init_sha1_starts(&ctx); */
/*   init_sha1_update(&ctx, tmp_hash, SHA1_CHECKSUM_LEN); */
/*   init_sha1_finish(&ctx, visor_init_hash); */
/*   putbytes(visor_init_hash, SHA1_CHECKSUM_LEN); */

  putstr("Hash of TrustVisor's init section:\n");
  init_sha1_starts(&ctx);
  init_sha1_update(&ctx, (u8*)visor_relocate_addr, slb_length);
  init_sha1_finish(&ctx, visor_init_hash);
  putbytes(visor_init_hash, SHA1_CHECKSUM_LEN);

  putstr("Expected PCR-17 value:\n");
  init_sha1_starts(&ctx);
  init_sha1_update(&ctx, tmp_hash, SHA1_CHECKSUM_LEN);
  init_sha1_update(&ctx, visor_init_hash, SHA1_CHECKSUM_LEN);
  init_sha1_finish(&ctx, tmp_hash);
  putbytes(tmp_hash, SHA1_CHECKSUM_LEN);

/*   putstr("Dump first and last 20 bytes of VISOR_INIT:\n"); */
/*   putbytes((u8*)visor_relocate_addr, 20); */
/*   putbytes((u8*)visor_relocate_addr + SKINIT_SLB_SIZE - 20, 20); */
  
  
  return;
}

/* Look for microcode patch to apply following SKINIT.  Returns the
 * address to which the microcode patch has been relocated, or zero if
 * none or error. */
u32 relocate_ucode(module_t *mod_array, u32 mods_count)
{
    u32 ucode_relocate_addr, ucode_size;    
    /* ASSUME microcode is always the last module */
    u32 mod_index = mods_count-1;

    /* Relocate microcode, if present, to UCODE_RELOCATE */
    if(*((u32*)mod_array[mod_index].mod_start) == UCODE_MAGIC){
        putstr2((char *)mod_array[mod_index].string, " is AMD Microcode patch; relocating.\n");
        
        ucode_relocate_addr = (u32)UCODE_RELOCATE;
        ucode_size = mod_array[mod_index].mod_end - mod_array[mod_index].mod_start;
        if(ucode_size > UCODE_MAX_SIZE) ucode_size = UCODE_MAX_SIZE;
        if(ucode_relocate_addr + ucode_size < ucode_relocate_addr)
            EARLY_FAIL();
        *((u32*)ucode_relocate_addr) = ucode_size;
        memcpy((void*)(ucode_relocate_addr+4), (void*)mod_array[mod_index].mod_start, 
               ucode_size);

/*         putstr("Microcode relocated; number of bytes (little endian!), first 32 bytes of image; "); */
/*         putbytes((u8*)&ucode_size, sizeof(u32)); */
/*         putbytes((u8*)ucode_relocate_addr, 32); */

        return ucode_relocate_addr;
    }

    return 0;
}

u32 relocate_kernel(module_t *mod_array, u32 mods_count)
{
  struct linux_setup_header *h;
  u32 setup_size, system_size, image_start, initrd_relocate_addr;
  u32 initrd_size;
  u32 x;

  image_start = mod_array[1].mod_start;
  h = (struct linux_setup_header*)(image_start + OFFSET);

  if ( (h->header != HEADER) ){
    EARLY_FAIL();
  }

  if ( (h->version < MIN_BOOTPROTO_VER) ){
    EARLY_FAIL();
  }
  
  /* the setup code executes in real mode. all of the setup (code,
   * header, command line, heap, and stack) is designed to occupy one
   * segment (64K). In DOS parlance, setup is a .com
   * program. Documentation/i386/boot.txt recommends the following
   * layout for the setup segment: 
   * offset 0x0000 - 0x7fff: setup code and header 
   * offset 0x8000 - 0x8fff: stack and heap 
   * offset 0x9000 - 0x90ff: command line 
   * we relocate setup to a segment starting at 0x10000 (lowest
   * address at to which setup can be relocated, according to
   * Documentation/i386/boot.txt) and create the recommended segment
   * layout.
   */
  if ( h->setup_sects == 0 )
    setup_size = 4;
  else
    setup_size = h->setup_sects + 1;
  setup_size *= SECTOR_SIZE;

  if (setup_size > 64 * 1024)
    EARLY_FAIL();

  memcpy((void *)SETUP_RELOCATE, (void *)(image_start), setup_size);
  h = (struct linux_setup_header*)(SETUP_RELOCATE + OFFSET);

  /* copy 32-bit kernel code to 0x100000 (1MB). the 32-bit kernel starts 
   * at location (setup_sects+1)*SECTOR_SIZE in the kernel image.
   */
  system_size = (mod_array[1].mod_end - mod_array[1].mod_start) 
                 - setup_size;
  image_start += (setup_size);
  if(system_size > LOADER_START - SYSTEM_RELOCATE)
    EARLY_FAIL();
  memcpy((void *)SYSTEM_RELOCATE, (void*)image_start, system_size);
  
  /* copy the kernel command line to offset 0x9000. max size of command line is
   * 255 bytes, excluding the trailing '\0' 
   */
  x = SETUP_RELOCATE + LINUX_BOOT_SP;
  strncpy((char *)x, (char*)mod_array[1].string, (u32)256);
  /* write location of command line in setup header. note that command line
   * is at physical address 0x19000 and thus will not get overwritten when
   * setup relocates itself to 0x90000
   */
  h->cmd_line_ptr = (u32)(SETUP_RELOCATE + LINUX_BOOT_SP);

  /* Relocate initrd, if present, to INITRD_RELOCATE */
  if(mods_count > 2) {
      if(*((u32*)mod_array[2].mod_start) == INITRD_MAGIC) {
          putstr2((char *)mod_array[2].string, " is INITRD; relocating.\n");
          initrd_relocate_addr = (u32)INITRD_RELOCATE;
          initrd_size = mod_array[2].mod_end - mod_array[2].mod_start;   
          putstr("initrd_size:\n");
          putbytes((u8*)&initrd_size, sizeof(u32));
          if(initrd_relocate_addr + initrd_size < initrd_relocate_addr)
              EARLY_FAIL();
          memcpy((void*)initrd_relocate_addr, (void*)mod_array[2].mod_start, 
                 initrd_size);    
          /* write location and size of initrd in setup header */
          h->ramdisk_image = initrd_relocate_addr;
          h->ramdisk_size = initrd_size;
          h->initrd_addr_max = INITRD_RELOCATE << 1;
      }
  }
  
  /* initialize other required fields of the setup header 
   * see Documentation/i386/boot.txt for details
   */
  h->vid_mode = (u16)NORMAL;
  h->type_of_loader = (u8)OTHER;
  /* offset limit of heap in real mode segment. leave space for a 
   * 512 byte stack at the end of heap, as recommended by 
   * Documentation/i386/boot.txt.
   */
  h->heap_end_ptr = (u16)(LINUX_BOOT_SP - 0x200); 
  h->loadflags = (u8)CAN_USE_HEAP;
  if( h->setup_sects == 0)
    h->setup_sects = 4;

  return 0;
}
