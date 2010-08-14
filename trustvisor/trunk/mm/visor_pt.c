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

/* visor_pt.c routines for setting up and handling TrustVisor's page tables
 * Written for TrustVisor by Ning Qu and Arvind Seshadri
 */

#include <types.h>
#include <error.h>
#include <print.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <svm.h>

void init_visor_pt(void) __attribute__ ((section ("_init_text")));

void init_visor_pt(void)
{
  u64 flags;
  u32 i, j;
  u32 addr, y;
  pdt_t pdt;
  pdpt_t pdpt;
  extern u32 visor_pdp_table[];
  extern u32 visor_pd_table[];

  y = __pa((u32)visor_pdp_table);
  pdpt = (pdpt_t)y;
  flags = (u64)(_PAGE_PRESENT);
  /* initalize the pdpt */
  for(i = 0; i < PAE_PTRS_PER_PDPT; i ++){
    y = (u32)__pa((u32)visor_pd_table + (i << PAGE_SHIFT_4K));
    pdpt[i] = pae_make_pdpe((u64)y, flags);
  }
 
  /* initialize the 4 pdt with unity mappings for the address range
   * 0-4GB. This should enable TrustVisor access up to 4GB to physical
   * addresses.
   */
  j  = ADDR_4GB >> (PAE_PDT_SHIFT);
  flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_ACCESSED | _PAGE_DIRTY 
		| _PAGE_PSE);
  y = __pa((u32)visor_pd_table);
  pdt = (pdt_t)y;
  for(i = 0, addr = 0; i < j; i ++, addr += PAGE_SIZE_2M)
    pdt[i] = pae_make_pde_big((u64)addr, flags);

  /* now modify the mappings for the virtual address range 
   * VISOR_RUNTIME_START --- VISOR_RUNTIME_START + VISOR_RUNTIME_SIZE
   * to point to physical addresses where TrustVisor is relocated
   */  
  y = (VISOR_RUNTIME_START) >> PAE_PDPT_SHIFT;
  pdt = (pdt_t)(__pa((u32)visor_pd_table) + (y << PAGE_SHIFT_4K));
  flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_ACCESSED | _PAGE_DIRTY
		| _PAGE_PSE);
  y = pae_get_pdt_index(VISOR_RUNTIME_START);
  for (i = 0, addr = visor_relocate_address; i < (VISOR_RUNTIME_SIZE >> PAE_PDT_SHIFT); 
	i ++, addr += PAGE_SIZE_2M)
    pdt[y + i] = pae_make_pde_big((u64)addr, flags);

  /* next modify the mapping for the virtual address range near the top
   * of RAM to point to the physical address range VISOR_RUNTIME_START
   * - VISOR_RUNTIME_START + VISOR_RUNTIME_SIZE
   */
  y = (visor_relocate_address) >> PAE_PDPT_SHIFT;
  pdt = (pdt_t)(__pa((u32)visor_pd_table) + (y << PAGE_SHIFT_4K));
  flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_ACCESSED | _PAGE_DIRTY
		| _PAGE_PSE);
  y = pae_get_pdt_index(visor_relocate_address);
  for (i = 0, addr = VISOR_RUNTIME_START; i < (VISOR_RUNTIME_SIZE >> PAE_PDT_SHIFT); 
	i ++, addr += PAGE_SIZE_2M)
    pdt[y + i] = pae_make_pde_big((u64)addr, flags);

  return;
}
   
