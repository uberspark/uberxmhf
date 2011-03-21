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

// Dervied from step4.c by
// 1. Fixing adversary to be PGCL program and adding top level guarded command
// 2. Replacing s_pt with P[i].P[j], 
// 3. Commenting out s_pt pointer code which isn't modelled in PGCL

#define GUEST_PHYSICALMEMORY_LIMIT	 (4096*2)
#define GUEST_VIRTUALMEMORY_LIMIT	 (4096*2)

//shadow_guest_CR3=0;

//ShadowVisor == shadow_page_fault || shadow_invalidate_page || shadow_new_context || adversary 

adversary() {
  for i 
    P[i].F[gPDE] = *;
       for j
          P[i].P[j].F[gPTE] = *;
}


shadow_page_fault(cr2){

  i = (cr2 >> 22);
  j  = ((cr2 & 0x003FFFFF) >> 12);

  
/*   if( (P[i].F[gPDE_PAGE_PRESENT]) && !(P[i].F[gPDE_PAGE_PSE])) { */
/*     s_pt = ((P[i]) & (~(PAGE_SIZE_4K - 1))); */
/*   } */


  if (P[i].F[gPDE_PAGE_PRESENT] && 
      P[i].F[gPDE_PAGE_PSE] && 
      (((P[i].F[gPDE] & (~(PAGE_SIZE_4K - 1))) + PAGE_SIZE_4M) < GUEST_PHYSICALMEMORY_LIMIT)){
      P[i].F[sPDE] = P[i].F[gPDE];
    }
  }


  if ( (P[i].F[gPDE_PAGE_PRESENT]) && 
       (!(P[i].F[gPDE_PAGE_PSE]) ) && 
       (P[i].P[j].F[gPTE_PAGE_PRESENT])) {

    P[i] = (( ((P[i]) & (~(PAGE_SIZE_4K - 1)))) & (~((PAGE_SIZE_4K - 1)))) | ((P[i].F[gPDE]) & (PAGE_SIZE_4K - 1)) ;

    if( ((P[i].P[j].F[gPTE] & (~(PAGE_SIZE_4K - 1))) + PAGE_SIZE_4K) < GUEST_PHYSICALMEMORY_LIMIT){
      // P[i].P[j].F[sPTE]
      s_pt[j] = P[i].P[j].F[gPTE]; 
    }
  }
}



shadow_invalidate_page( address){
  
  i = (address >> 22);
  j  = ((address & 0x003FFFFF) >> 12);
  

  if (P[i].F[gPDE_PAGE_PRESENT] && 
      P[i].F[gPDE_PAGE_PRESENT] &&     
      !P[i].F[gPDE_PAGE_PSE] && 
      !P[i].F[gPDE_PAGE_PSE] )  {
    //s_pt = ((P[i]) & (~(PAGE_SIZE_4K - 1)));
    //s_pt[j].F[sPTE] = 0;
    P[i].P[j].F[sPTE] = 0;
  }


  if( (P[i].F[gPDE_PAGE_PRESENT] && !P[i].F[gPDE _PAGE_PRESENT]) || 
      (P[i].F[gPDE_PAGE_PRESENT] && P[i].F[gPDE_PAGE_PRESENT] &&     
      (P[i].F[gPDE_PAGE_PSE] || P[i].F[gPDE_PAGE_PSE]))) {
    P[i].F[sPDE] = 0;
  }
  
}



shadow_new_context( guest_CR3 ){

   shadow_guest_CR3 = guest_CR3;

   num_pagedir_entries = GUEST_VIRTUALMEMORY_LIMIT / (4096*1023);
  
   for (i = 0; i < num_pagedir_entries; i++) {
     P[i] = 0;
   }
}

