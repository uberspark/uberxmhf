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
 * ugcpust verification driver
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfgeec.h>
//#include <xmhf-debug.h>

#include <uapi_gcpustate.h>

u32 cpuid = 0;	//BSP cpu

//////
// frama-c non-determinism functions
//////

u32 Frama_C_entropy_source;

//@ assigns Frama_C_entropy_source \from Frama_C_entropy_source;
void Frama_C_update_entropy(void);

u32 framac_nondetu32(void){
  Frama_C_update_entropy();
  return (u32)Frama_C_entropy_source;
}

u32 framac_nondetu32interval(u32 min, u32 max)
{
  u32 r,aux;
  Frama_C_update_entropy();
  aux = Frama_C_entropy_source;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}


//////
u32 check_esp, check_eip = CASM_RET_EIP;
slab_params_t test_sp;


void hwm_vdriver_cpu_vmwrite(u32 encoding, u32 value){
/*	if(test_sp.src_slabid != XMHFGEEC_SLAB_GEEC_PRIME){
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_CONTROL_VMX_SECCPU_BASED	);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL	);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH	);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL	);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH	);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_CONTROL_EPT_POINTER_FULL	);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_CONTROL_EPT_POINTER_HIGH	);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_CR0			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_CR3			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_CR4			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_FS_BASE			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_GS_BASE			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_TR_BASE			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_GDTR_BASE			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_IDTR_BASE			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_SYSENTER_ESP		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_SYSENTER_EIP		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_RSP			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_RIP			);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_SYSENTER_CS		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_IA32_EFER_FULL		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_ES_SELECTOR		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_CS_SELECTOR		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_SS_SELECTOR		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_DS_SELECTOR		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_FS_SELECTOR		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_GS_SELECTOR		);
		//@assert !(test_sp.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME) && !(encoding == VMCS_HOST_TR_SELECTOR		);
	}
*/

	if(test_sp.src_slabid != XMHFGEEC_SLAB_GEEC_PRIME){
		if(	( encoding == VMCS_CONTROL_VMX_SECCPU_BASED	||
			 encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL	||
			 encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH	||
			 encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL	||
			 encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH	||
			 encoding == VMCS_CONTROL_EPT_POINTER_FULL	||
			 encoding == VMCS_CONTROL_EPT_POINTER_HIGH	||
			 encoding == VMCS_HOST_CR0			||
			 encoding == VMCS_HOST_CR3			||
			 encoding == VMCS_HOST_CR4			||
			 encoding == VMCS_HOST_FS_BASE			||
			 encoding == VMCS_HOST_GS_BASE			||
			 encoding == VMCS_HOST_TR_BASE			||
			 encoding == VMCS_HOST_GDTR_BASE			||
			 encoding == VMCS_HOST_IDTR_BASE			||
			 encoding == VMCS_HOST_SYSENTER_ESP		||
			 encoding == VMCS_HOST_SYSENTER_EIP		||
			 encoding == VMCS_HOST_RSP			||
			 encoding == VMCS_HOST_RIP			||
			 encoding == VMCS_HOST_SYSENTER_CS		||
			 encoding == VMCS_HOST_IA32_EFER_FULL		||
			 encoding == VMCS_HOST_ES_SELECTOR		||
			 encoding == VMCS_HOST_CS_SELECTOR		||
			 encoding == VMCS_HOST_SS_SELECTOR		||
			 encoding == VMCS_HOST_DS_SELECTOR		||
			 encoding == VMCS_HOST_FS_SELECTOR		||
			 encoding == VMCS_HOST_GS_SELECTOR		||
			 encoding == VMCS_HOST_TR_SELECTOR)
		){
			//@assert 0;
		}
	}

}


void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = _slab_tos[cpuid];
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

	test_sp.src_slabid = framac_nondetu32interval(0, XMHFGEEC_TOTAL_SLABS-1);
	test_sp.dst_uapifn = framac_nondetu32();
	test_sp.in_out_params[0] = 0; 	test_sp.in_out_params[1] = 0;
	test_sp.in_out_params[2] = 0; 	test_sp.in_out_params[3] = 0;
	test_sp.in_out_params[4] = 0; 	test_sp.in_out_params[5] = 0;
	test_sp.in_out_params[6] = 0; 	test_sp.in_out_params[7] = 0;
	test_sp.in_out_params[8] = 0; 	test_sp.in_out_params[9] = 0;
	test_sp.in_out_params[10] = 0; 	test_sp.in_out_params[11] = 0;
	test_sp.in_out_params[12] = 0; 	test_sp.in_out_params[13] = 0;
	test_sp.in_out_params[14] = 0; 	test_sp.in_out_params[15] = 0;

	//execute harness: TODO
	slab_main(&test_sp);


	//@assert xmhfhwm_cpu_gprs_esp == check_esp;
	//@assert xmhfhwm_cpu_gprs_eip == check_eip;
}


