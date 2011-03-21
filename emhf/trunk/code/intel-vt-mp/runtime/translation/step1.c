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

// Derived from base.c by 
// 1. Removing all types 

#include <types.h>
#include <paging.h>
#include <shadow_paging_npae.h>


#define GUEST_PHYSICALMEMORY_LIMIT	 (4096*2)  //4MB guest PA
#define GUEST_VIRTUALMEMORY_LIMIT	 (4096*2)  //4GB guest VA 

 s_pd_t[1024];
 __shadow_npae_p_tables[1024];

 shadow_guest_CR3=0;


shadow_page_fault( cr2){

   index_pdt, index_pt; 
   flags, paddr;
    s_pt;

   gPDE = nondet_();
   gPTE = nondet_();


  index_pdt = (cr2 >> 22);
  index_pt  = ((cr2 & 0x003FFFFF) >> 12);

  
  if( (s_pd_t[index_pdt] & _PAGE_PRESENT) && !(s_pd_t[index_pdt] & _PAGE_PSE)) {
    s_pt = ()((s_pd_t[index_pdt]) & (~(PAGE_SIZE_4K - 1)));
  }



  if ((gPDE & _PAGE_PRESENT) && (gPDE & _PAGE_PSE) ) {

    if( (  ((gPDE) & (~(PAGE_SIZE_4K - 1))) + PAGE_SIZE_4M) < GUEST_PHYSICALMEMORY_LIMIT){
      s_pd_t[index_pdt] = gPDE;
    }
  }



  if ( (gPDE & _PAGE_PRESENT) && (!(gPDE & _PAGE_PSE) ) && (gPTE & _PAGE_PRESENT)) {

    flags = ((gPDE) & (PAGE_SIZE_4K - 1));
    paddr = ((s_pd_t[index_pdt]) & (~(PAGE_SIZE_4K - 1)));
	
    s_pd_t[index_pdt] = ((paddr) & (~((PAGE_SIZE_4K - 1)))) | (flags);

    if( (((gPTE) & (~(PAGE_SIZE_4K - 1))) + PAGE_SIZE_4K) < GUEST_PHYSICALMEMORY_LIMIT){
      s_pt[index_pt] = gPTE; 
    }
  }
}



shadow_invalidate_page( address){
  
   s_pt;

   gPDE = nondet_();
   gPTE = nondet_();

   index_pdt = (address >> 22);
   index_pt  = ((address & 0x003FFFFF) >> 12);
  

  if ((s_pd_t[index_pdt] & _PAGE_PRESENT) && (gPDE & _PAGE_PRESENT) &&     
      (!(gPDE & _PAGE_PSE)) && (!(s_pd_t[index_pdt] & _PAGE_PSE)) )  {
    s_pt = ((s_pdt_t[index_pdt]) & (~(PAGE_SIZE_4K - 1)));
    s_pt[index_pt] = 0;

  }


  if( ((s_pd_t[index_pdt] & _PAGE_PRESENT) && (!(gPDE & _PAGE_PRESENT))) || 
      
      ((s_pd_t[index_pdt] & _PAGE_PRESENT) && (gPDE & _PAGE_PRESENT) &&     
       ((gPDE & _PAGE_PSE) || ( s_pd_t[index_pdt] & _PAGE_PSE)))        ) {

    s_pd_t[index_pdt] = 0;

  }
  
}



shadow_new_context( guest_CR3 ){

   shadow_guest_CR3 = guest_CR3;

   num_pagedir_entries = GUEST_VIRTUALMEMORY_LIMIT / (4096*1023);
  
  for (i= 0; i < num_pagedir_entries; i++) {
    s_pd_t[i] = 0;
  }
}

