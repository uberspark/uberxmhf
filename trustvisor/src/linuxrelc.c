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

// linuxrelc.c
// linux kernel/initrd relocate and bootstrap
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

/*
	grub_debug
	linux_data_real_addr=0x00090000
	LINUX_BZIMAGE_ADDR=0x00100000
	lh->version=0x020a
	lh->heap_end_ptr=0x8e00;
	lh->loadflags=0x81
	lh->cmd_line_ptr=0x00099000
	setup size=0x3400;
	system size = 0x3384c0
	initrd size = 0xd1e47c
	initrd base= 0x372d1000


*/

// setup header for the Linux/i386 boot protocol version 2.04  
// requires kernel version 2.6.14 or later. starts at offset 0x1f1 
// in the kernel image. 

#define OFFSET 							0x1f1 			//offset of setup header in setup code 
#define SECTOR_SIZE 				512					//size of a disk sector
#define HEADER 							0x53726448  //linux kernel magic header
#define MIN_BOOTPROTO_VER 	0x0204			//minimum boot-protocol version we support is 2.04
#define SETUP_RELOCATE 			0x10000 		//physical memory address where setup code goes
#define SYSTEM_RELOCATE 		0x100000		//physical memory address where 32-bit kernel goes

//we assume guest to be allocated 1GB (1024M) of physical memory
//we further assume that initrd/initramfs does not exceed 48M in size
//#define INITRD_RELOCATE 		0x372d1000 	//1GB - 48M
#define INITRD_RELOCATE 		0x4000000 	
//#define INITRD_MAXADDR			0x37ffffff	
#define INITRD_MAXADDR			0x4FFFFFF	

#define NORMAL 							0xffff 			//vga mode
#define OTHER 							0xff 				//bootloader type
#define CAN_USE_HEAP 				0x81 				//loadflag to indicate that heap is usable

//kernel command line to be passed
//char linux_kernel_cmdline[] = "ro root=/dev/sda8 resume=/dev/sda10 maxcpus=1 mem=1024M no_console_suspend earlyprintk=1"; 
char linux_kernel_cmdline[] = "ro root=/dev/sda2 maxcpus=1 mem=1024M"; 

struct linux_setup_header {
  u8 setup_sects;		
  u16 root_flags;		
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


/*
void linux_store_setupandinitrd(u32 setupbase, u32 setupsize, u32 initrdbase,
		u32 initrdsize, char *cmdline_untrusted, char *cmdline_trusted){
	extern u32 __linux_setup_image[], __linux_initrd_image[];
	extern u32 __linux_kernel_cmdline_untrusted[], __linux_kernel_cmdline_trusted[];		
	
	ASSERT(setupsize < __LINUX_OS_SETUP_SIZE);
	ASSERT(initrdsize < __LINUX_OS_INITRD_SIZE);
	
	memcpy((void *)__linux_setup_image, setupbase, setupsize);
	memcpy((void *)__linux_initrd_image, initrdbase, initrdsize);
	strncpy((char *)__linux_kernel_cmdline_untrusted, cmdline_untrusted, (u32)256);
	strncpy((char *)__linux_kernel_cmdline_trusted, cmdline_trusted, (u32)256);
		
}*/

//---relocate linux kernel 
//void relocate_kernel(u32 setupbase, u32 setupsize, u32 initrdbase, u32 initrdsize){
void relocate_kernel(u32 vmlinuz_base, u32 vmlinuz_size, 
			u32 initrd_base, u32 initrd_size){
  
	struct linux_setup_header *h;
  u32 setup_size, setup_base= SETUP_RELOCATE;
	u32 system_size, system_base = SYSTEM_RELOCATE;
  
	//initialize linux kernel header located at OFFSET from vmlinuz_base
	h = (struct linux_setup_header*)(vmlinuz_base + OFFSET);

  //some sanity checks
	if ( (h->header != HEADER) ){
    printf("\nHeader mismatch. Halting");
		HALT();
  }
  if ( (h->version < MIN_BOOTPROTO_VER) ){
    printf("\nBoot-protocol version mismatch. Halting!");
    HALT();
  }

	//determine "setup" size  
  //the "setup" code executes in real mode. all of the setup (code,
  //header, command line, heap, and stack) is designed to occupy one
  //segment (64K). 
	//offset 0x0000 - 0x7fff: setup code and header 
  //offset 0x8000 - 0x8fff: stack and heap 
  //offset 0x9000 - 0x90ff: command line 
  
	if ( h->setup_sects == 0 )
    setup_size = 4;
  else
    setup_size = h->setup_sects + 1;
  setup_size *= SECTOR_SIZE;

	ASSERT(setup_size < (64*1024) );	//setup_size _MUST_ be within 64K
	printf("\n	setup at 0x%08x, size=0x%08x", setup_base, setup_size);

	//copy 16-bit setup code to setup_base
  memcpy((void *)setup_base, (void *)(vmlinuz_base), setup_size);

	//determine "system" size
	system_size = vmlinuz_size - setup_size;
  printf("\n	system at 0x%08x, size=0x%08x", system_base, system_size);
	
	//copy 32-bit kernel code to system_base i.e 0x100000 (1MB)
  memcpy((void *)system_base, (void*)(vmlinuz_base + setup_size), system_size);


  printf("\n	initrd at 0x%08x, size=0x%08x", INITRD_RELOCATE, initrd_size);
	
	//copy initrd
  memcpy((void*)INITRD_RELOCATE, (void*)initrd_base,  initrd_size);
	
  //copy the kernel command line to offset 0x9000. max size of command line is
  //255 bytes, excluding the trailing '\0' 
  memset((void *)(setup_base+0x9000), 0, 256);
	memcpy((void *)(setup_base+0x9000), &linux_kernel_cmdline, sizeof(linux_kernel_cmdline));
	printf("\n	cmdline at 0x%08x, size=%u bytes", (setup_base+0x9000), sizeof(linux_kernel_cmdline));

	//re-initialize linux kernel header pointer to the new setup code
	//at setup_base
	h = (struct linux_setup_header*)(setup_base + OFFSET);
	
	//write location of command line in setup header. note that command line
  //is at physical address 0x19000 and thus will not get overwritten when
  //setup relocates itself to 0x90000
  h->cmd_line_ptr = (u32)(setup_base + 0x9000);
  
  //write location and size of initrd in setup header 
  h->ramdisk_image = INITRD_RELOCATE;
  h->ramdisk_size = initrd_size;
  h->initrd_addr_max = INITRD_MAXADDR;
  
  // initialize other required fields of the setup header 
  // see Documentation/x86/boot.txt for details
  h->vid_mode = (u16)NORMAL;
  h->type_of_loader = (u8)OTHER;
  
	//offset limit of heap in real mode segment. leave space for a 
  //512 byte stack at the end of heap, as recommended by 
  //Documentation/x86/boot.txt.
  h->heap_end_ptr = (u16)(0x9000 - 0x200); 
  h->loadflags = (u8)CAN_USE_HEAP;

  if( h->setup_sects == 0)
    h->setup_sects = 4;

  return;
}

//---setuplinuxboot
void setuplinuxboot(VCPU *vcpu, u32 vmlinuz_base, u32 vmlinuz_size, 
		u32 initrd_base, u32 initrd_size){


	relocate_kernel(vmlinuz_base, vmlinuz_size, initrd_base, initrd_size);
	printf("\nCPU(0x%02x): relocated and setup linux kernel...", vcpu->id);
	
	//setup VMCS for linux real-mode setup code
	vcpu->vmcs.guest_DS_selector = 0x1000;
	vcpu->vmcs.guest_DS_base = vcpu->vmcs.guest_DS_selector * 16;
	vcpu->vmcs.guest_ES_selector = 0x1000;
	vcpu->vmcs.guest_ES_base = vcpu->vmcs.guest_ES_selector * 16;
	vcpu->vmcs.guest_FS_selector = 0x1000;
	vcpu->vmcs.guest_FS_base = vcpu->vmcs.guest_FS_selector * 16;
	vcpu->vmcs.guest_GS_selector = 0x1000;
	vcpu->vmcs.guest_GS_base = vcpu->vmcs.guest_GS_selector * 16;
	vcpu->vmcs.guest_SS_selector = 0x1000;
	vcpu->vmcs.guest_SS_base = vcpu->vmcs.guest_SS_selector * 16;
	vcpu->vmcs.guest_RSP = 0x9000;
	vcpu->vmcs.guest_CS_selector = 0x1020;
	vcpu->vmcs.guest_CS_base = vcpu->vmcs.guest_CS_selector * 16;
	vcpu->vmcs.guest_IDTR_base = 0x0;	
	vcpu->vmcs.guest_IDTR_limit = 0xffff;	
	vcpu->vmcs.guest_RIP=0;
	vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_IF);

  return;
}
