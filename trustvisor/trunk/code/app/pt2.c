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

#include <emhf.h> /* FIXME: narrow this down so this can be compiled
                     and tested independently */
#include <pt2.h>
#include <pages.h>

/* for a given virtual address range, return an array of page-map-entry-objects */
/* returned size may be larger than the requested size, in which case
   the last returned pmeo contains "extra" address-range. it's up to
   the caller to splinter that last page if necessary. */
/* *pmeos_num should be set by caller to the size of pmeos. if the
   return-value is non-zero, pmeos_of_range ran out of room;
   *pmeos_num is set to the number of pmeos that would have been
   written. */
/* XXX need to think through concurrency issues. e.g., should caller
   hold a lock? */
/* int pmeos_of_range(hpt_pmeo_t pmeos[], size_t *pmeos_num, */
/*                    hpt_pmo_t* pmo_root, hpt_walk_ctx_t *walk_ctx, */
/*                    hpt_va_t base, size_t *size) */
/* { */
/*   size_t offset; */
/*   size_t pmeos_maxnum = *pmeos_num; */
  
/*   *pmeos_num = 0; */

/*   while (offset < *size) { */
/*     hpt_va_t va = base + offset; */
/*     size_t page_size; */
/*     hpt_pmeo_t pmeo; */

/*     ASSERT(*pmeos_num < pmeos_maxnum); */

/*     hpt_walk_get_pmeo(&pmeo, */
/*                       walk_ctx, */
/*                       pmo_root, */
/*                       1, */
/*                       va); */
/*     /\* XXX need to add support to hpt to get size of memory mapped by */
/*        a page *\/ */
/*     ASSERT(pmeo.lvl == 1); */
/*     page_size = PAGE_SIZE_4K; */
/*     offset += page_size; */

/*     if (*pmeos_num < pmeos_maxnum) { */
/*       pmeos[*pmeos_num] = pmeo; */
/*     } */
/*     (*pmeos_num)++; */
/*   } */

/*   *size = offset; /\* may be larger than requested *\/ */

/*   if(*pmeos_num <= pmeos_maxnum) { */
/*     return 0; */
/*   } else { */
/*     return 1; */
/*   } */
/* } */

/* /\* nested-page-map-entry-objects of guest-page-map-entry-objects *\/ */
/* void npmeos_of_gpmeos(hpt_walk_ctx_t *reg_npm_ctx, */
/*                       hpt_pmo_t* reg_npmo_root, */
/*                       hpt_pmeo_t npmeos[], size_t *npmeos_num, */
/*                       hpt_pmeo_t gpmeos[], size_t gpmeos_num) */
/* { */
/*   size_t gpmeos_i; */

/*   for(gpmeos_i=0; gpmeos_i < gpmeos_num; gpmeos_i++) { */
    
/*   } */
/* } */


/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'f */
/* tab-width:2      */
/* End:             */
