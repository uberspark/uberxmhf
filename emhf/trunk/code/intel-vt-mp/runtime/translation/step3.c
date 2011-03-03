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

#include <types.h>
#include <paging.h>
#include <shadow_paging_npae.h>


#define GUEST_PHYSICALMEMORY_LIMIT	 (4096*2)  //4MB guest PA
#define GUEST_VIRTUALMEMORY_LIMIT	 (4096*2)  //4GB guest VA 


shadow_guest_CR3=0;


shadow_page_fault(cr2){

  index_pdt = (cr2 >> 22);
  index_pt  = ((cr2 & 0x003FFFFF) >> 12);


  P[index_pdt].F[gPDE] = nondet_();
  P[index_pdt].P[index_pt].F[gPTE] = nondet_();

  
  if( (P[index_pdt].F[gPDE_PAGE_PRESENT]) && !(P[index_pdt].F[gPDE_PAGE_PSE])) {
    s_pt = ((P[index_pdt]) & (~(PAGE_SIZE_4K - 1)));
  }


  if ((P[index_pdt].F[gPDE_PAGE_PRESENT]) && (P[index_pdt].F[gPDE_PAGE_PSE]) ) {

    if( (  ((P[index_pdt].F[gPDE]) & (~(PAGE_SIZE_4K - 1))) + PAGE_SIZE_4M) < GUEST_PHYSICALMEMORY_LIMIT){
      P[index_pdt] = P[index_pdt].F[gPDE];
    }
  }


  if ( (P[index_pdt].F[gPDE].F[_PAGE_PRESENT]) && 
       (!(P[index_pdt].F[gPDE_PAGE_PSE]) ) && 
       (P[index_pdt].P[index_pt].F[gPTE_PAGE_PRESENT])) {

    flags = ((P[index_pdt].F[gPDE]) & (PAGE_SIZE_4K - 1));
    paddr = ((P[index_pdt]) & (~(PAGE_SIZE_4K - 1)));
	
    P[index_pdt] = ((paddr) & (~((PAGE_SIZE_4K - 1)))) | (flags);

    if( (((P[index_pdt].P[index_pt].F[gPTE]) & (~(PAGE_SIZE_4K - 1))) + PAGE_SIZE_4K) < GUEST_PHYSICALMEMORY_LIMIT){
      s_pt[index_pt] = P[index_pdt].P[index_pt].F[gPTE]; 
    }
  }
}



shadow_invalidate_page( address){
  
  P[index_pdt].F[gPDE] = nondet_();
  P[index_pdt].P[index_pt].F[gPTE] = nondet_();

  index_pdt = (address >> 22);
  index_pt  = ((address & 0x003FFFFF) >> 12);
  

  if ((P[index_pdt].F[gPDE_PAGE_PRESENT]) && (P[index_pdt].F[gPDE_PAGE_PRESENT]) &&     
      (!(P[index_pdt].F[gPDE_PAGE_PSE])) && (!(P[index_pdt].F[gPDE_PAGE_PSE])) )  {
    s_pt = ((P[index_pdt]) & (~(PAGE_SIZE_4K - 1)));
    s_pt[index_pt].F[sPTE] = 0;

  }


  if( ((P[index_pdt].F[gPDE_PAGE_PRESENT]) && (!(P[index_pdt].F[gPDE _PAGE_PRESENT]))) || 
      
      ((P[index_pdt].F[gPDE_PAGE_PRESENT]) && (P[index_pdt].F[gPDE_PAGE_PRESENT]) &&     
       ((P[index_pdt].F[gPDE_PAGE_PSE]) || ( P[index_pdt].F[gPDE_PAGE_PSE])))        ) {

    P[index_pdt].F[gPDE] = 0;
  }
  
}



shadow_new_context( guest_CR3 ){

   shadow_guest_CR3 = guest_CR3;

   num_pagedir_entries = GUEST_VIRTUALMEMORY_LIMIT / (4096*1023);
  
  for (i = 0; i < num_pagedir_entries; i++) {
    P[i] = 0;
  }
}

