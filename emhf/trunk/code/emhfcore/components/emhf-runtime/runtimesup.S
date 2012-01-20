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

// runtime support structures
// author: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h> 



	
	.extern g_e820map
	.extern g_cpumap	
	.extern g_runtime_TSS
	
	.extern g_svm_dev_bitmap

	.extern g_vmx_vtd_pdp_table
	.extern g_vmx_vtd_pd_tables
	.extern g_vmx_vtd_p_tables
	.extern g_vmx_vtd_ret
	.extern g_vmx_vtd_cet
	
	.extern cstartup
	.extern allcpus_common_start
	.extern runtime_exception_handler
	
	.extern emhf_xcphandler_idt
	.extern emhf_xcphandler_exceptionstubs

//------------------------------------------------------------------------------
//RUNTIME PARAMETER BLOCK DATA
//------------------------------------------------------------------------------
//NOTE: The definition here _MUST_ match declaration of RPB in target.h	
	.section .s_rpb
	.global _rpb
_rpb:
	.long RUNTIME_PARAMETER_BLOCK_MAGIC
	.long cstartup
	.long x_3level_pdpt
	.long	x_3level_pdt
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long x_init_stack
	.long 8192
	.long x_gdt
	.long 0 //.extern nwadapterstructure
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long emhf_xcphandler_idt
	.long emhf_xcphandler_exceptionstubs
	.long 32
	.long 0 //x_e1000desc
	.long 0 //x_e1000header
	.long 0 //x_e1000body
  .global __ha
  __ha:
	.long 0  //physical base address of runtime
	.long 0  //virtual base address of runtime
	.long 0  //2M aligned size of runtime
	.long g_e820map				   //system E820 map
	.long 0                  //number of entries
	.long g_cpumap		       //system CPU map
	.long 0                  //number of entries
	.long g_runtime_TSS			 //runtime TSS
	.long	g_svm_dev_bitmap	 //runtime SVM DEV bitmap
	.long g_vmx_vtd_pdp_table	//runtime VMX(VT-d) DMA protection page-tables
	.long g_vmx_vtd_pd_tables
	.long g_vmx_vtd_p_tables
	.long g_vmx_vtd_ret				//runtime VMX(VT-d) DMA protection Root Entry Table
	.long g_vmx_vtd_cet				//runtime VMX(VT-d) DMA protection Context Entry Table 
	.long 0, 0, 0, 0				//32 bytes for field uart_config of type uart_config_t 
	.long 1							//isEarlyInit, 1 = early init, 0 = late init (default to early init)

//------------------------------------------------------------------------------
//STACK (LOCAL)
//------------------------------------------------------------------------------
	
	.section .stack
x_init_stack:
	.fill	8192, 1, 0




