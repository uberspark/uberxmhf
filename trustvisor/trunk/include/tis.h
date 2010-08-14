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

/*
 * \brief   TIS data structures and header of tis.c
 * \date    2006-03-28
 * \author  Bernhard Kauer <kauer@tudos.org>
 */
/*
 * Copyright (C) 2006  Bernhard Kauer <kauer@tudos.org>
 * Technische Universitaet Dresden, Operating Systems Research Group
 *
 * This file is part of the OSLO package, which is distributed under
 * the  terms  of the  GNU General Public Licence 2.  Please see the
 * COPYING file for details.
 */
/**
 * Modified by Jonathan M. McCune for use with Flicker in 2007.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2.0 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#ifndef _TIS_H_
#define _TIS_H_

enum tis_init
  {
    TIS_INIT_NO_TPM  = 0,
    TIS_INIT_STM = 1,
    TIS_INIT_INFINEON = 2,
    TIS_INIT_BROADCOM = 3,
    TIS_INIT_OTHERS = 9
  };


enum tis_mem_offsets
  {
/*     TIS_BASE =  (int) 0xfed40000, */
    TPM_DID_VID_0 = 0xf00,
    TIS_LOCALITY_0 = 0x0000,
    TIS_LOCALITY_1 = 0x1000,
    TIS_LOCALITY_2 = 0x2000,
    TIS_LOCALITY_3 = 0x3000,
    TIS_LOCALITY_4 = 0x4000
  };


struct tis_id
{
  int did_vid;
  unsigned char rid;
} __attribute__((packed));


/* See Chapter 10 of TPM Interface Specification */
struct tis_mmap
{
    unsigned char  access;          /* 0 */
    unsigned char  __dummy1[7];     /* 7-1 */
    unsigned int   int_enable;      /* b-8 */
    unsigned char  int_vector;      /* c */
    unsigned char  __dummy2[3];     /* f-d */
    unsigned int   int_status;      /* 13-10 */
    unsigned int   intf_capability; /* 17-14 */
    unsigned char  sts_base;        /* 18 */
    unsigned short sts_burst_count; /* 1a-19 */
    unsigned char  __dummy3[9];     /* 23-1b */
    unsigned char  data_fifo;       /* 24 */
} __attribute__((packed));


enum tis_access_bits
{
    TIS_ACCESS_VALID    = 1<<7, /* 80 */
    TIS_ACCESS_RESERVED = 1<<6, /* 40 */
    TIS_ACCESS_ACTIVE   = 1<<5, /* 20 */
    TIS_ACCESS_SEIZED   = 1<<4, /* 10 */
    TIS_ACCESS_TO_SEIZE = 1<<3, /* 08 */
    TIS_ACCESS_PENDING  = 1<<2, /* 04 */
    TIS_ACCESS_REQUEST  = 1<<1, /* 02 */
    TIS_ACCESS_TOS      = 1<<0  /* 01 */
};


enum tis_sts_bits
{
    TIS_STS_VALID       = 1<<7, /* 80 */
    TIS_STS_CMD_READY   = 1<<6, /* 40 */
    TIS_STS_TPM_GO      = 1<<5, /* 20 */
    TIS_STS_DATA_AVAIL  = 1<<4, /* 10 */
    TIS_STS_EXPECT      = 1<<3, /* 08 */
    TIS_STS_RESERVED_2  = 1<<2, /* 04 */
    TIS_STS_RETRY       = 1<<1, /* 02 */
    TIS_STS_RESERVED_0  = 1<<0  /* 01 */
};


int initsec_prepare_tpm(void) __attribute__ ((section ("_init_text")));
int initsec_tis_transmit(unsigned char *buffer, unsigned int write_count, unsigned int read_count, int locality) __attribute__ ((section ("_init_text")));

void slb_tis_dump(void);
enum tis_init slb_tis_init(void);
int slb_tis_deactivate_all(void);
int slb_tis_access(int locality, int force);
int slb_tis_transmit(unsigned char *buffer, unsigned write_count,
                     unsigned read_count, int locality);

int slb_tis_read(unsigned char *buffer,
                 unsigned int size, int locality);
int slb_tis_write(const unsigned char *buffer,
                  unsigned int size, int locality);
void slb_wait_state(volatile struct tis_mmap *mmap, unsigned state);

unsigned long TIS_BASE(void);

#define slb_out_description(x, y) printf(x" %#x\n", y)
#define slb_outchar(x) printf("%c", x)
#define slb_outbyte(x) printf("%x", x)
#define slb_out_info(x) printf(x"\n")
#define slb_out_string(x) printf(x"\n")

#if 0
#define slb_assert(X) {if (!(X)) { slb_out_string("Assertion failed"); }}
#else
#define slb_assert(X)
#endif

#define ERROR(result, value, msg) \
  { if (value) { slb_out_string(msg);  }}

#define slb_memcpy(dest, src, n)	memcpy(dest, src, n)

#define slb_wait(n)	mdelay(n)

#define CHECK3(result, value, msg) \
  {	if (value) { slb_out_info(msg);	return result; }}

#endif
