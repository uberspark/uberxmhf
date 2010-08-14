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

/* debug.h - Declarations and constants for handling x86 debug registers */
/* Written for TrustVisor by Arvind Seshadri */
#ifndef __DEBUG_H__
#define __DEBUG_H__

#define EXECUTE 0
#define WRITE   1
#define IORW    2
#define R_OR_W  3

#define BYTE  0
#define WORD  1
#define QWORD 2
#define DWORD 3

#define VMCB_DR6_OFFSET 0x568
#define VMCB_DR7_OFFSET 0x560

#ifndef __ASSEMBLY__
typedef union
{
  u32 reg;
  struct
  {
    u32 b0:    1;
    u32 b1:    1;
    u32 b2:    1;
    u32 b3:    1;
    u32 resv1: 8;
    u32 resv2: 1;
    u32 bd:    1;
    u32 bs:    1;
    u32 bt:    1;
    u32 resv3: 16;
  }fields;
} __attribute__ ((packed)) dr6_t;

typedef union
{
  u32 reg;
  struct
  {
    u32 l0:    1;
    u32 g0:    1;
    u32 l1:    1;
    u32 g1:    1;
    u32 l2:    1;
    u32 g2:    1;
    u32 l3:    1;
    u32 g3:    1;
    u32 le:    1;
    u32 ge:    1;
    u32 resv1: 3;
    u32 gd:    1;
    u32 resv2: 2;
    u32 rw0:   2;
    u32 len0:  2;
    u32 rw1:   2;
    u32 len1:  2;
    u32 rw2:   2;
    u32 len2:  2;
    u32 rw3 :  2;
    u32 len3:  2;
  }fields;
} __attribute__ ((packed)) dr7_t;
#endif /* __ASSEMBLY__ */

#endif /* __DEBUG_H__ */
