// linuxrelc.c
// linux kernel/initrd relocate and bootstrap
// author: amit vasudevan (amitvasudevan@acm.org)
#include <types.h>
#include <target.h>
#include <print.h>
#include <multiboot.h>
#include <str.h>
#include <error.h>


/* setup header for the Linux/i386 boot protocol version 2.04  
 * requires kernel version 2.6.14 or later. starts at offset 0x1f1 
 * in the kernel image. 
 */ 

#define OFFSET 		0x1f1 	/* offset of setup header in setup code */
#define SECTOR_SIZE 	512
#define HEADER 		0x53726448
#define MIN_BOOTPROTO_VER 0x0204
#define SETUP_RELOCATE 	0x10000 /* address to which setup code is relocated */
#define SYSTEM_RELOCATE 0x100000	/* relocation address for 32-bit kernel */
//#define INITRD_RELOCATE 0x08000000 	// initrd relocated base
#define INITRD_RELOCATE 0x37cf0000 	// initrd relocated base
//#define INITRD_MAXADDR	(INITRD_RELOCATE+0x00400000)	//4MB maximum size
#define INITRD_MAXADDR	0x38000000
#define NORMAL 		0xffff 	/*vga mode */
#define OTHER 		0xff 	/* bootloader type */
#define CAN_USE_HEAP 	0x80 	/* loadflag to indicate that heap is usable */



struct linux_setup_header
{
  u8 setup_sects;		/* size of setup in 512 byte sectors */
  u16 root_flags;		/* mount root read-only */
  u32 syssize;
  u16 ramsize;
  u16 vid_mode;
  u16 root_dev;
  u16 boot_flag;
  u16 jump;
  u32 header;
  u16 version;
  u32 realmode_switch;
  u16 start_sys;
  u16 kernel_version;
  u8 type_of_loader;
  u8 loadflags;
  u16 setup_move_size;
  u32 code32_start;
  u32 ramdisk_image;
  u32 ramdisk_size;
  u32 bootsect_kludge;
  u16 heap_end_ptr;
  u16 pad1;
  u32 cmd_line_ptr;
  u32 initrd_addr_max;
} __attribute__ ((packed));


u32 relocate_kernel(module_t *mod_array, u32 mods_count)
{
  struct linux_setup_header *h;
  u32 setup_size, system_size, image_start, initrd_relocate_addr;
  u32 initrd_size;
  u32 x;
  
  image_start = mod_array[1].mod_start;
  h = (struct linux_setup_header*)(image_start + OFFSET);

  if ( (h->header != HEADER) ){
    printf("\nHeader mismatch. Halting");
		HALT();
  }

  if ( (h->version < MIN_BOOTPROTO_VER) ){
    printf("\nBoot-protocol version mismatch. Halting!");
    HALT();
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

  if (setup_size > 64 * 1024){
		printf("\nsetup size > 64M, halt!");
		HALT();
	}

  memcpy((void *)SETUP_RELOCATE, (void *)(image_start), setup_size);
  h = (struct linux_setup_header*)(SETUP_RELOCATE + OFFSET);

  /* copy 32-bit kernel code to 0x100000 (1MB). the 32-bit kernel starts 
   * at location (setup_sects+1)*SECTOR_SIZE in the kernel image.
   */
  system_size = (mod_array[1].mod_end - mod_array[1].mod_start) 
                 - setup_size;
  image_start += (setup_size);
  printf("\nLinux system size= %u bytes", system_size);
	//if(system_size > LOADER_START - SYSTEM_RELOCATE)
  //  EARLY_FAIL();
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
  
  /* relocate initrd, if present, to INITRD_RELOCATE */
  if(mods_count == 3){
    printf("\nRelocating initrd...");
		initrd_relocate_addr = (u32)INITRD_RELOCATE;
    initrd_size = mod_array[2].mod_end - mod_array[2].mod_start;   
    if((mod_array[2].mod_start + initrd_size) > initrd_relocate_addr){
			printf("\nblah, initrd size error. halting!");
			HALT();
		}
    memcpy((void*)initrd_relocate_addr, (void*)mod_array[2].mod_start, 
	   initrd_size);    
    /* write location and size of initrd in setup header */
    h->ramdisk_image = initrd_relocate_addr;
    h->ramdisk_size = initrd_size;
    h->initrd_addr_max = INITRD_MAXADDR;
  
		printf("\nramdisk start=0x%08x, size=0x%08x, max=0x%08x", 
			h->ramdisk_image, h->ramdisk_size, h->initrd_addr_max);
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

extern u32 realmode_start[];
extern u32 realmode_end[];

void relocate(multiboot_info_t *mbt){
  module_t *mod_array = (module_t*)mbt->mods_addr;
  u32 mods_count = mbt->mods_count;

  // relocate Linux kernel and initrd/initramfs 
  if ( relocate_kernel(mod_array, mods_count) ){
    printf("\nUnable to relocate linux kernel and/or initrd. Halting!");
    HALT();
  }

  /* move 16 bit real-mode code to fixed address */
  memcpy((void *)LOADER_REAL_START, &realmode_start, 
	 (u32)&realmode_end - (u32)&realmode_start);

  return;
}
