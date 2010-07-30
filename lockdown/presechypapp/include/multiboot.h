/* multiboot.h header for multiboot spec
 * Written for SecVisor by Arvind Seshadri
 */

#ifndef __MULTIBOOT_H_
#define __MULTIBOOT_H_

#define MULTIBOOT_HEADER_MAGIC 0x1badb002
/* bootloader should load modules page aligned */
#define ALIGNED 0x00 
/* bootloader should pass the mem limits info in the mem_* fields 
 * of the multiboot struct. Note that this does not require
 * the bootloader to pass a valid memory map in the mmap_* fields.
 * Since SecVisor requires a memory map in the e820 format, we should 
 * check if the mmap_* fields are valid
 */

#define MEM_INFO 0x01
#define MULTIBOOT_HEADER_FLAGS ((1<<ALIGNED)|(1<<MEM_INFO))

/* this vaule is present in %eax when the kernel is called a by 
 * a multiboot-compliant bootloader.
 */
#define MULTIBOOT_BOOTLOADER_MAGIC 0x2badb002

/* multiboot info structure flags */
#define MBI_MEMLIMITS  0x00
#define MBI_DRIVES     0x01
#define MBI_CMDLINE    0x02
#define MBI_MODULES    0x03
#define MBI_MEMMAP     0x06

#ifndef __ASSEMBLY__
/* symbol table for a.out */
typedef struct{
  u32 tabsize;
  u32 strsize;
  u32 addr;
  u32 reserved;
} aout_symbol_table_t;

/* section header table for ELF */
typedef struct{
  u32 num;
  u32 size;
  u32 addr;
  u32 shndx;
} elf_section_header_table_t;

/* multiboot information struct */
typedef struct{
  u32 flags;
  u32 mem_lower;
  u32 mem_upper;
  u32 boot_device;
  u32 cmdline;
  u32 mods_count;
  u32 mods_addr;
  union{
    aout_symbol_table_t aout_sym;
    elf_section_header_table_t elf_sec;
  }u;
  u32 mmap_length;
  u32 mmap_addr;
} multiboot_info_t;

/* The module structure.  */
typedef struct {
  u32 mod_start;
  u32 mod_end;
  u32 string;
  u32 reserved;
} module_t;

/* The memory map. NOTE: offset 0 is base_addr_low and not size.  */
typedef struct {
  u32 size;
  u32 base_addr_low;
  u32 base_addr_high;
  u32 length_low;
  u32 length_high;
  u32 type;
} __attribute__((packed)) memory_map_t;
#endif /*__ASSEMBLY*/

#endif /* __MULTIBOOT_H */
