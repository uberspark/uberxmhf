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

#include "pages.h"

#include <types.h>
#include <puttymem.h>
#include <paging.h>
#include <error.h>

void pagelist_init(pagelist_t *pl)
{
  const int pages = 64;
  pl->buf = vmalloc(pages*PAGE_SIZE_4K);
  ASSERT(pl->buf != NULL);

  pl->page_base = (void*)PAGE_ALIGN_UP4K((uintptr_t)pl->buf);
  pl->num_allocd =
    (pl->page_base == pl->buf)
    ? pages
    : pages-1;
 
  pl->num_used = 0;
}

void* pagelist_get_page(pagelist_t *pl)
{
  void *page;

  /* we'll handle allocating more on-demand later */
  ASSERT(pl->num_used < pl->num_allocd);

  page = pl->page_base + (pl->num_allocd*PAGE_SIZE_4K);
  pl->num_used++;

  return page;
}

void* pagelist_get_zeroedpage(pagelist_t *pl)
{
  void *page = pagelist_get_page(pl);
  memset(page, 0, PAGE_SIZE_4K);
  return page;
}

void pagelist_free_all(pagelist_t *pl)
{
  vfree(pl->buf);
  pl->buf=NULL;
  pl->num_allocd=0;
}
