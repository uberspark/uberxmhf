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

#ifndef HPT_CONSTS_H
#define HPT_CONSTS_H

/* HPT_<page table type>_<name>_L<applicable levels>_[M][P]_[LO|HI|BIT] */
/* P if the mapping is valid for entries mapping a page.
 * M if the mapping is valid for entries mapping another map (table)
 * when there's no ambiguity, the same macro may include level 1 and 'M',
 * even though a level 1 entry is always a page. e.g., '...L21_MP...'
 * for a name that is valid for l2 maps, l2 pages, and l1 pages.
 *
 * Including in the name of each macro which levels and types it is
 * valid for is intended to help write error-free code below. e.g., it
 * is clear when using an 'L32_M' macro that one must first ensure that
 * the PTE being dealt with maps a map\table and is of level 3 or 2.
 * 
 */
#define HPT_NORM_ADDR_L2_M_HI 31
#define HPT_NORM_ADDR_L2_M_LO 12
#define HPT_NORM_ADDR3122_L2_P_HI 31
#define HPT_NORM_ADDR3122_L2_P_LO 22
#define HPT_NORM_MBZ21_L2_P_BIT 21
#define HPT_NORM_ADDR3932_L2_P_HI 20
#define HPT_NORM_ADDR3932_L2_P_LO 13
#define HPT_NORM_PAT_L2_P_BIT 12 /* page attribute table */
#define HPT_NORM_ADDR_L1_P_HI 31
#define HPT_NORM_ADDR_L1_P_LO 12
#define HPT_NORM_AVL11_L21_MP_HI 11 /* available */
#define HPT_NORM_AVL11_L21_MP_LO 9 
#define HPT_NORM_G_L21_P_BIT 8 /* global */
#define HPT_NORM_IGN8_L2_M_BIT 8
#define HPT_NORM_PS_L2_MP_BIT 7 /* page size */
#define HPT_NORM_PAT_L1_P_BIT 7 /* page attribute table */
#define HPT_NORM_D_L21_P_BIT 6 /* dirty (valid for lowest lvl only) */
#define HPT_NORM_IGN6_L2_M_BIT 6
#define HPT_NORM_A_L21_MP_BIT 5 /* accessed */
#define HPT_NORM_PCD_L21_MP_BIT 4 /* page cache disable */
#define HPT_NORM_PWT_L21_MP_BIT 3 /* page write through */
#define HPT_NORM_US_L21_MP_BIT 2 /* 0:supervisor 1:user */
#define HPT_NORM_RW_L21_MP_BIT 1 /* 0:read-only 1:read\write */
#define HPT_NORM_P_L21_MP_BIT 0 /* present */

#define HPT_PAE_MBZ63_L3_MP_BIT 63
#define HPT_PAE_NX_L21_MP_BIT 63
#define HPT_PAE_MBZ62_L321_MP_HI 62
#define HPT_PAE_MBZ62_L321_MP_LO 52
#define HPT_PAE_ADDR_L321_M_HI 51 /* address bits */
#define HPT_PAE_ADDR_L321_M_LO 12
#define HPT_PAE_ADDR_L2_P_HI 51
#define HPT_PAE_ADDR_L2_P_LO 13
#define HPT_PAE_PAT_L2_P_BIT 12
#define HPT_PAE_ADDR_L1_P_HI 51 /* address bits */
#define HPT_PAE_ADDR_L1_P_LO 12
#define HPT_PAE_AVL11_L321_MP_HI 11 /* available */
#define HPT_PAE_AVL11_L321_MP_LO 9
#define HPT_PAE_MBZ8_L3_MP_HI 8
#define HPT_PAE_MBZ8_L3_MP_LO 5
#define HPT_PAE_G_L21_P_BIT 8 /* global */
#define HPT_PAE_IGN8_L2_M_BIT 8
#define HPT_PAE_PS_L2_MP_BIT 7 /* page size */
#define HPT_PAE_PAT_L1_P_BIT 7 /* page attribute table */
#define HPT_PAE_D_L21_P_BIT 6 /* dirty */
#define HPT_PAE_IGN6_L2_M_BIT 6
#define HPT_PAE_A_L21_P_BIT 5 /* accessed */
#define HPT_PAE_PCD_L321_MP_BIT 4 /* page cache disable */
#define HPT_PAE_PWT_L321_MP_BIT 3 /* page write through */
#define HPT_PAE_MBZ2_L3_M_HI 2
#define HPT_PAE_MBZ2_L3_M_LO 1
#define HPT_PAE_US_L21_MP_BIT 2 /* 0:supervisor 1:user */
#define HPT_PAE_RW_L21_MP_BIT 1 /* 0:read-only 1:read\write */
#define HPT_PAE_P_L321_MP_BIT 0 /* present */

#define HPT_LONG_NX_L4321_MP_BIT 63
#define HPT_LONG_AVL62_L4321_MP_HI 62
#define HPT_LONG_AVL52_L4321_MP_LO 52
#define HPT_LONG_ADDR_L4321_M_HI 51 /* address bits */
#define HPT_LONG_ADDR_L4321_M_LO 12
#define HPT_LONG_ADDR_L32_P_HI 51
#define HPT_LONG_ADDR_L32_P_LO 13
#define HPT_LONG_ADDR_L1_P_HI 51
#define HPT_LONG_ADDR_L1_P_LO 12
#define HPT_LONG_PAT_L32_P_BIT 12
#define HPT_LONG_AVL11_L4321_MP_HI 11 /* available */
#define HPT_LONG_AVL11_L4321_MP_LO 9
#define HPT_LONG_MBZ8_L4_MP_BIT 8
#define HPT_LONG_MBZ7_L4_MP_BIT 7
#define HPT_LONG_G_L21_P_BIT 8 /* global */
#define HPT_LONG_PS_L32_MP_BIT 7 /* page size */
#define HPT_LONG_PAT_L1_P_BIT 7 /* page attribute table */
#define HPT_LONG_IGN6_L4_M_BIT 6
#define HPT_LONG_D_L321_P_BIT 6 /* dirty */
#define HPT_LONG_A_L4321_MP_BIT 5 /* accessed */
#define HPT_LONG_PCD_L4321_MP_BIT 4 /* page cache disable */
#define HPT_LONG_PWT_L4321_MP_BIT 3 /* page write through */
#define HPT_LONG_US_L4321_MP_BIT 2 /* 0:supervisor 1:user */
#define HPT_LONG_RW_L4321_MP_BIT 1 /* 0:read-only 1:read\write */
#define HPT_LONG_P_L4321_MP_BIT 0 /* present */

#define HPT_EPT_MAXPHYADDR 52 /* FIXME, should find this dynamically
                                 using cpuid, cf Intel manual 3A
                                 4.1.4. using the max value of 52,
                                 which could cause trouble if the
                                 reserved bitfield above MAXPHYADDR
                                 gets used for anything. */
#define HPT_EPT_AVL63_L4321_MP_HI 63
#define HPT_EPT_AVL52_L4321_MP_LO 52
#define HPT_EPT_ADDR_L4321_MP_HI (HPT_EPT_MAXPHYADDR-1)
#define HPT_EPT_ADDR_L4321_MP_LO 12
#define HPT_EPT_AVL11_L4321_MP_HI 11
#define HPT_EPT_AVL11_L4321_MP_LO 8
#define HPT_EPT_MBZ7_L4_M_BIT 7
#define HPT_EPT_PS_L32_MP_BIT 7
#define HPT_EPT_AVL7_L1_P_BIT 7
#define HPT_EPT_IPAT_L321_P_BIT 6
#define HPT_EPT_MBZ6_L432_M_HI 6
#define HPT_EPT_MBZ6_L432_M_LO 3
#define HPT_EPT_MT_L321_P_HI 5
#define HPT_EPT_MT_L321_P_LO 3
#define HPT_EPT_X_L4321_MP_BIT 2
#define HPT_EPT_W_L4321_MP_BIT 1
#define HPT_EPT_R_L4321_MP_BIT 0
#define HPT_EPT_PROT_L4321_MP_HI 2
#define HPT_EPT_PROT_L4321_MP_LO 0

#define HPT_CR3_PML4_LONG_HI 51
#define HPT_CR3_PML4_LONG_LO 12
#define HPT_CR3_PML2_LONG_MBZ11_HI 11
#define HPT_CR3_PML2_LONG_MBZ11_LO 5
#define HPT_CR3_PML3_PAE_HI 31
#define HPT_CR3_PML3_PAE_LO 5
#define HPT_CR3_PML2_NORM_HI 31
#define HPT_CR3_PML2_NORM_LO 12
#define HPT_CR3_MBZ11_NORM_HI 11
#define HPT_CR3_MBZ11_NORM_LO 5
#define HPT_CR3_PCD_BIT 4
#define HPT_CR3_PWT_BIT 3
#define HPT_CR3_MBZ2_HI 2
#define HPT_CR3_MBZ2_LO 0

#define HPT_EPTP_MBZ63_H 63
#define HPT_EPTP_MBZ63_L HPT_EPT_MAXPHYADDR
#define HPT_EPTP_PML4_HI (HPT_EPT_MAXPHYADDR-1)
#define HPT_EPTP_PML4_LO 12
#define HPT_EPTP_MBZ11_HI 11
#define HPT_EPTP_MBZ11_LO 6
#define HPT_EPTP_PWLM1_HI 5
#define HPT_EPTP_PWLM1_LO 3
#define HPT_EPTP_PSMT_HI 2
#define HPT_EPTP_PSMT_LO 0

#define HPT_CR4_PAE_BIT 5
#define HPT_CR4_PSE_BIT 4

#endif
