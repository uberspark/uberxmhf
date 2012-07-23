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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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
 * EMHF base platform component interface, x86 vmx backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//initialize CPU state
void emhf_baseplatform_arch_x86vmx_cpuinitialize(void){
    	u32 bcr0;
	    txt_heap_t  __attribute__((unused)) *txt_heap;
        os_mle_data_t __attribute__((unused)) *os_mle_data ;
  
	    //set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
		bcr0 = read_cr0();
		bcr0 |= 0x20;
		write_cr0(bcr0);

#if defined (__DRTM_DMA_PROTECTION__)
        // restore pre-SENTER MTRRs that were overwritten for SINIT launch 
        // NOTE: XXX TODO; BSP MTRRs ALREADY RESTORED IN SL; IS IT
        //   DANGEROUS TO DO THIS TWICE? 
        // sl.c unity-maps 0xfed00000 for 2M so these should work fine 
        txt_heap = get_txt_heap();
        printf("\ntxt_heap = 0x%08x", (u32)txt_heap);
        os_mle_data = get_os_mle_data_start(txt_heap);
        printf("\nos_mle_data = 0x%08x", (u32)os_mle_data);
    
        if(!validate_mtrrs(&(os_mle_data->saved_mtrr_state))) {
             printf("\nSECURITY FAILURE: validate_mtrrs() failed.\n");
             HALT();
        }
        restore_mtrrs(&(os_mle_data->saved_mtrr_state));
#endif
      
}
