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

/*
 * EMHF base platform component interface, x86 common backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <emhf.h>


//generic x86 platform reboot
void emhf_baseplatform_arch_x86_reboot(void){
	//u8 nullidt[] = {0x0, 0x0, 0x0, 0x0, 0x0, 0x0};

    //zero out IDT
	emhf_xcphandler_resetIDT();
	
	{
	  volatile u32 *icr_low = (u32 *)(0xFEE00000 + 0x300);
	  volatile u32 *icr_high = (u32 *)(0xFEE00000 + 0x310);
	  u32 icr_high_value= 0xFFUL << 24;
	  u32 delivered;	
  
      *icr_high = icr_high_value;    //send to all but self
      printf("\n%s: firing reboot NMIs...", __FUNCTION__);
	  *icr_low = 0x000C0400UL;      //send NMI        
  
	  //check if IPI has been delivered successfully
	  do{
		delivered = *icr_high;
		delivered &= 0x00001000;
	  }while(delivered);
	}
	
	//load IDT of 0 size
	//__asm__ __volatile__ ("lidtl %0\r\n" : : "m" (*nullidt) );
	
	printf("\n%s: reboot!", __FUNCTION__);
	//step-3: execute ud2 instruction to generate triple fault
	__asm__ __volatile__("ud2 \r\n");
	
	//never get here
	printf("\n%s: should never get here. halt!", __FUNCTION__);
	HALT();
}


//reboot platform
void emhf_baseplatform_arch_reboot(VCPU *vcpu){
	ASSERT (vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD)
		emhf_baseplatform_arch_x86svm_reboot(vcpu);
	else //CPU_VENDOR_INTEL
		emhf_baseplatform_arch_x86vmx_reboot(vcpu);
}
