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

/* relocate.h header file for Linux kernel relocation 
 * Written for TrustVisor by Arvind Seshadri
 */

#ifndef __RELOCATE_H__
#define __RELOCATE_H__

/* setup header for the Linux/i386 boot protocol version 2.04  
 * requires kernel version 2.6.14 or later. starts at offset 0x1f1 
 * in the kernel image. 
 */ 

#define OFFSET 0x1f1 /* offset of setup header in setup code */
#define SECTOR_SIZE 512
#define HEADER 0x53726448
#define MIN_BOOTPROTO_VER 0x0204
#define SETUP_RELOCATE 0x10000 /* address to which setup code is relocated */
#define SYSTEM_RELOCATE 0x100000 /* relocation address for 32-bit kernel */
#define INITRD_RELOCATE 0x4000000 /* relocate initrd to 64MB */
#define NORMAL 0xffff /*vga mode */
#define OTHER 0xff /* bootloader type */
#define CAN_USE_HEAP 0x80 /* loadflag to indicate that heap is usable */

#ifndef __ASSEMBLY__

struct linux_setup_header
{
  u8 setup_sects;                       /* size of setup in 512 byte sectors */
  u16 root_flags;                       /* mount root read-only */
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

#endif /* __ASSEMBLY__ */

#endif /* __RELOCATE_H__ */
