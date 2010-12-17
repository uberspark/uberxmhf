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

//libsechyp - SecHyp library routines for applications
//author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <target.h>

#include <_libsechyp.h>
#include <globals.h>

static void __set_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] |= (1 << bit_offset);

  return;                        
}

static void __clear_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] &= ~(1 << bit_offset);

  return;
}

static u32 __test_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  if (bit_vector[byte_offset] & (1 << bit_offset))
    return 1;
  else 
    return 0;
}

//---IOPM Bitmap interface------------------------------------------------------
void sechyp_iopm_set_write(VCPU *vcpu, u32 port, u32 size){
  u32 i;

  for (i = 0; i < size; i ++)
    __set_page_prot((port+i), (u8 *)g_svm_iopm);
}

//---MSRPM Bitmap interface------------------------------------------------------
void sechyp_msrpm_set_write(VCPU *vcpu, u32 msr){
  u32 byte_offset, bit_offset;

  if ((msr >= (u32)0xC0000000) && (msr < (u32)0xC0002000))
    msr = (msr - (u32)0xC0000000) + 0x2000;
  else if ((msr >= (u32)0xC0010000) && (msr < (u32)0xC0012000))
    msr = (msr - (u32)0xC0010000) + 0x4000;
  
  // each msr covers 2 bits, one for read and one for write 
  byte_offset = (msr << 1) / 8;
  bit_offset = (msr << 1) & 7;
  g_svm_msrpm[byte_offset] |= (1 << (bit_offset + 1));
}

