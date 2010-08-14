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

/* prot.h: Macros, functions, and definitions for handling the x86
 * GDT, LDT, and IDT.  
 * Written by Ning Qu and Arvind Seshadri.
 */

#ifndef __PROT_H__
#define __PROT_H__

#define TI_GDT 0
#define TI_LDT 1

#define SEG_SEL_INDEX(sel)	((u16)(sel) >> 3)
#define SEG_SEL_TI(sel)		(((u16)(sel) & 0x4) >> 2)
#define SEG_SEL_RPL(sel)	((u16)(sel) & 0x3)
#define SEG_CHG_RPL(sel, rpl)	((sel) = (((u16)(sel) & ~0x3) | rpl))

#ifndef __ASSEMBLY__
/* pseudo descriptor for gdtr and idtr */
typedef struct pseudo_descriptor {
  u16	     limit;
  u64        base;
} __attribute__ ((packed)) pseudo_descriptor_t;

typedef union generic_segment_descriptor {
  u64 bytes;
  struct
  {
    u64 limit0:    16;    
    u64 base0:     16;    
    u64 base16:    8;
    u64 type:      4;
    u64 s:         1;
    u64 dpl:       2;
    u64 p:         1;
    u64 limit16:   4;
    u64 avl:       1;
    u64 resvd1:    1;
    u64 db:        1;
    u64 g:         1;
    u64 base24:    8;
  } fields;
} __attribute__ ((packed)) generic_segment_descriptor_t;

typedef union interrupt_gate_descriptor {
  u64 bytes;
  struct
  {
    u64 offset0:    16;    
    u64 selector:  16;    
    u64 resvd0:    8;
    u64 type:      4;
    u64 s:         1;
    u64 dpl:       2;
    u64 p:         1;
    u64 offset16:  16;
  } fields;
} __attribute__ ((packed)) interrupt_gate_descriptor_t;

typedef generic_segment_descriptor_t *sgd_t;
typedef pseudo_descriptor_t *xdt_t;

#define SEG_SET_BASE(entry, vaddr)	\
  ({								\
     (entry)->fields.base0 = ((vaddr) & 0xffff); 		\
     (entry)->fields.base16 = ((u64)(vaddr) >> 16) & 0xff; 	\
     (entry)->fields.base24 = ((u64)(vaddr) >> 24) & 0xff; 	\
  })

#define SEG_GET_BASE(entry)	\
   ((u32)(((entry).fields.base0 & 0xffff) | (((entry).fields.base16 & 0xff) << 16) | (((entry).fields.base24 & 0xff) << 24)))
#define SEG_GET_OFFSET(entry)	\
   ((u32)(((entry).fields.offset0 & 0xffff) | (((entry).fields.offset16 & 0xffff) << 16)))

#define SEG_CHANGE_DPL(entry, dpl)    ((entry)->fields.dpl = (dpl))

static inline void load_idtr(u32 val)
{
  __asm__("lidt %0": :"m" (val));
}

static inline u32 save_idtr(void)
{
  u32 val;

  __asm__("sidt %0":"=m" (val):);
 
  return val;
}

#endif /* __ASSEMBLY__ */

#endif /* __PROT_H__ */
