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

/* heap.c routines for managing the heap 
 * Written for TrustVisor by Arvind Seshadri
 */
#include <types.h>
#include <error.h>
#include <visor.h>
#include <paging.h>
#include <svm.h>
#include <print.h>
#include <heap.h>
#include <string.h>


static struct page_t *heap;
static u32 heap_size;   /* heap size in pages */
static u8 *heap_free;

void init_heap(void)
{
  extern u32 _visor_end[]; 
  u32 heap_start, heap_end, i;
  
  /* find the first page boundary after the end of bss */
  heap_start = ((u32)_visor_end & (~((u32)PAGE_SIZE_4K - 1))) + (u32)PAGE_SIZE_4K;
  
  /* find the page boundary at VISOR_RUNTIME_END */
  heap_end = ((u32)VISOR_RUNTIME_END) & (~((u32)PAGE_SIZE_4K - 1));
  
  /* we need a vector that indicates which pages in the heap are
   * available. i am using an array of unsigned char for this
   * vector. each int in the array corresponds to one page in the
   * heap.  since the total size of TrustVisor's memory region (code,
   * data stack, and heap) is 32MB, an 8KB region should be sufficient to
   * hold the array (32MB/4KB = 8192 entries and each entry is 1
   * byte). the allocation needs to be increased if TrustVisor's heap
   * grows bigger than 32MB or if the size of an element becomes > 1 bytes
   */

  /* allocate first two pages of heap to hold the heap_free vector */
  heap_free = (u8 *)heap_start;
  heap_start += (u32)(PAGE_SIZE_4K << 1);

  /* calculate heap_size */
  heap_size = ((heap_end - heap_start) >> PAGE_SHIFT_4K) + 1;
  heap = (struct page_t *)heap_start;
  
  /* mark all pages in heap available */
  for(i = 0; i < heap_size; i ++)
    heap_free[i] = YES;
  DEBUG printf("DEBUG: Initialized heap starting at 0x%08lx (size %d pages)\n",
	 (unsigned long)heap_start, heap_size);
  return;
}

u32 alloc_page(void)
{
  u32 i;
  
  for(i = 0; (!heap_free[i]) && (i < heap_size); i ++);

  if (i >= heap_size)
    return ((u32)0);
  
  heap_free[i] = NO;
  /* zero out allocated page, assuming page size is PAGE_SIZE_4K */
  memset(heap[i].array, 0, PAGE_SIZE_4K);
    
  return ((u32)(heap + i));
}

void free_page(u32 page)
{
  heap_free[(page - (u32)heap) >> PAGE_SHIFT_4K] = YES;
  return;
}

    
    
  
