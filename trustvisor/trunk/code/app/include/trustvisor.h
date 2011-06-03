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

#ifndef TRUSTVISOR_H
#define TRUSTVISOR_H

/* 
 * definition for scode sections info 
 * */
#define MAX_SECTION_NUM 10 
#define MAX_REGPAGES_NUM 50

enum scode_section_type
  {
    SECTION_TYPE_SCODE = 1,
    SECTION_TYPE_SDATA = 2,
    SECTION_TYPE_PARAM = 3,
    SECTION_TYPE_STACK = 4,
    SECTION_TYPE_STEXT = 5,

    /* internal */
    SECTION_TYPE_SHARED = 6,
    SECTION_TYPE_GUEST_PAGE_TABLES = 7
  };

/* 
 * definition for VMM call
 * */
enum VMMcmd {
  /* pal manipulation ops */
  VMMCMD_REG	=1,
  VMMCMD_UNREG	=2,

  /* uTPM ops */
  VMMCMD_SEAL	=3,
  VMMCMD_UNSEAL	=4,
  VMMCMD_QUOTE	=5,
  VMMCMD_SHARE	=6,
  VMMCMD_PCRREAD	=7,
  VMMCMD_PCREXT	=8,
  VMMCMD_GENRAND	=9,

  /* misc */
  VMMCMD_TEST		=255,
};

struct scode_sections_struct{
  enum scode_section_type type;
  unsigned int start_addr;
  int page_num; /* size of section in pages */
};

#define SCODE_MAX_SECTION_NUM 10  /* max sections that are allowed in scode registration */
struct scode_sections_info{
  int section_num;
  struct scode_sections_struct ps_str[SCODE_MAX_SECTION_NUM];
};

/* 
 * definition for scode param info 
 * */
/* parameter type */
enum scode_param_type
  {
    PM_TYPE_INTEGER = 1,
    PM_TYPE_POINTER = 2
  };
/* #define PM_TYPE_INTEGER 1 /\* integer *\/ */
/* #define PM_TYPE_POINTER 2 /\* pointer *\/ */


struct scode_params_struct{
  u32 type;  /* 1: integer ;  2:pointer*/
  u32 size;
};

#define MAX_PARAMS_NUM 10
struct scode_params_info{
  u32 params_num;
  struct scode_params_struct pm_str[MAX_PARAMS_NUM];
};

#endif
