/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
	ATAGS (ARM bootloader tags) definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __ATAGS_H__
#define __ATAGS_H__

// tag id's
// see http://www.simtec.co.uk/products/SWLINUX/files/booting_article.html#appendix_tag_reference

#define ATAG_NONE       0x00000000
#define ATAG_CORE       0x54410001
#define ATAG_MEM        0x54410002
#define ATAG_RAMDISK    0x54410004
#define ATAG_INITRD2    0x54420005
#define ATAG_SERIAL     0x54410006
#define ATAG_REVISION   0x54410007
#define ATAG_CMDLINE    0x54410009

#ifndef __ASSEMBLY__

/* structures for each atag */
struct atag_header {
        u32 size; /* length of tag in words including this header */
        u32 tag;  /* tag type */
}__attribute__((packed));

struct atag_core {
        u32 flags;
        u32 pagesize;
        u32 rootdev;
}__attribute__((packed));

struct atag_mem {
        u32     size;
        u32     start;
}__attribute__((packed));

struct atag_ramdisk {
        u32 flags;
        u32 size;
        u32 start;
}__attribute__((packed));

struct atag_initrd2 {
        u32 start;
        u32 size;
}__attribute__((packed));

struct atag_serialnr {
        u32 low;
        u32 high;
}__attribute__((packed));

struct atag_revision {
        u32 rev;
}__attribute__((packed));

struct atag_cmdline {
        u8    cmdline[1];
} __attribute__((packed));

struct atag {
        //struct atag_header hdr;
		u32 size;
		u32 tag;
        union {
                struct atag_core         core;
                struct atag_mem          mem;
                struct atag_ramdisk      ramdisk;
                struct atag_initrd2      initrd2;
                struct atag_serialnr     serialnr;
                struct atag_revision     revision;
                struct atag_cmdline      cmdline;
        } u;
} __attribute__((packed));


#define atag_next(t)     ((struct atag *)(((u32)t) + ((t)->size)*4))
#define atag_size(type)  ((sizeof(struct atag_header) + sizeof(struct type)) >> 2)

#endif // __ASSEMBLY__



#endif //__ATAGS_H__
