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

/* bitfield.h - bitfield utility functions
 * author - Jim Newsome (jnewsome@cmu.edu)
 *
 * Some utility functions for manipulating bits within 32 bit and 64
 * bit unsigned ints. These functions tend to be a bit more verbose
 * than doing the low-level operations directly, but they also help to
 * make the semantic meaning clearer, and to avoid subtle bugs that
 * tend to crop up.
 *
 * All of these functions are intended to be side-effect-free. In
 * particular, they return a new value rather than manipulating data
 * in place.
 */
#ifndef BITFIELD_H
#define BITFIELD_H

#include "error.h"
#include "types.h"

static inline u64 ZERO_HI64(u64 x, int bits)
{
  return ((x) << (bits) >> (bits));
}
static inline u64 ZERO_LO64(u64 x, int bits)
{
  return ((x) >> (bits) << (bits));
}
static inline u32 ZERO_HI32(u32 x, int bits)
{
  return ((x) << (bits) >> (bits));
}
static inline u32 ZERO_LO32(u32 x, int bits)
{
  return ((x) >> (bits) << (bits));
}

static inline u64 MASKRANGE64(int hi, int lo)
{
  return ZERO_LO64(ZERO_HI64(0xffffffffffffffffull,
                         64-(hi)-1),
                 (lo));
}

static inline u32 MASKRANGE32(int hi, int lo)
{
  return ZERO_LO32(ZERO_HI32(0xfffffffful,
                             32-(hi)-1),
                   (lo));
}

static inline u64 MASKBIT64(int bit)
{
  return 1ull<<bit;
}
static inline u32 MASKBIT32(int bit)
{
  return 1ul<<bit;
}



static inline u64 BR64_GET_HL(u64 x64, int hi, int lo)
{
  return ZERO_HI64(x64, 63-(hi)) >> (lo);
}
static inline u64 BR32_GET_HL(u32 x32, int hi, int lo)
{
  return ZERO_HI64(x32, 31-(hi)) >> (lo);
}

static inline u64 BR64_SET_HL(u64 x64, int hi, int lo, u64 val)
{
  ASSERT(ZERO_HI64(val, 63-(hi-lo)) == val);
  return ((x64 & ~MASKRANGE64((hi), (lo))) | ((val) << (lo)));
}
static inline u32 BR32_SET_HL(u32 x32, int hi, int lo, u32 val)
{
  ASSERT(ZERO_HI64(val, 31-(hi-lo)) == val);
  return ((x32 & ~MASKRANGE32((hi), (lo))) | ((val) << (lo)));
}

#define BR64_GET_BR(x64, name) BR64_GET_HL(x64, name##_HI, name##_LO)
#define BR64_SET_BR(x64, name, val) BR64_SET_HL(x64, name##_HI, name##_LO, val)

static inline unsigned int BR64_GET_BIT(u64 x64, int pos)
{
  return ((x64 & MASKRANGE64(pos, pos)) >> pos);
}
static inline u64 BR64_SET_BIT(u64 x64, int pos, bool val)
{
  u64 bit = val ? 1ull : 0ull;
  return (x64 & ~(0x1ull<<pos) | (bit<<pos));
}

/* offset == (dst_hi-src_hi) == (dst_lo-src_lo) */
static inline u64 BR64_COPY_BITS_HL(u64 dst, u64 src, int src_hi, int src_lo, int offset)
{
  return BR64_SET_HL(dst,
                     (src_hi)+(offset),
                     (src_lo)+(offset),
                     BR64_GET_HL(src, src_hi, src_lo));
}

/* offset == (dst_hi-src_hi) == (dst_lo-src_lo) */
static inline u32 BR32_COPY_BITS_HL(u32 dst, u32 src, int src_hi, int src_lo, int offset)
{
  return BR32_SET_HL(dst,
                     (src_hi)+(offset),
                     (src_lo)+(offset),
                     BR32_GET_HL(src, src_hi, src_lo));
}

#endif
