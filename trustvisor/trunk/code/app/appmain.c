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

// appmain.c
// emhf application main module
// author: amit vasudevan (amitvasudevan@acm.org)

//#include <target.h>
#include  "./include/puttymem.h"
#include  "./include/scode.h"
#include  <globals.h>

extern struct trustvisor_context * tv_ctx;

// a placeholder for now...
u32 emhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb){
	printf("\nCPU(0x%02x): Hello world from sechyp app!", vcpu->id);

#ifdef __MP_VERSION__
	if (g_isl->isbsp()) 
#endif
	{
		printf("[TV] CPU(0x%02x): init scode!\n", vcpu->id);
		init_scode(vcpu);


		//sanity checks
	//	ASSERT( apb->bootsector_size > 0 && apb->optionalmodule_size > 0 );

		if (apb->optionalmodule_ptr) {
			printf("\nCPU(0x%02x): vmlinuz b=0x%08x, size=%u bytes", vcpu->id,
					apb->bootsector_ptr, apb->bootsector_size);
			printf("\nCPU(0x%02x): initramfs b=0x%08x, size=%u bytes", vcpu->id,
					apb->optionalmodule_ptr, apb->optionalmodule_size);

			setuplinuxboot(vcpu, apb->bootsector_ptr, apb->bootsector_size, 
					apb->optionalmodule_ptr, apb->optionalmodule_size);
		}

	}

	return APP_INIT_SUCCESS;  //successful
}

u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r)
{	
	struct vmcb_struct * linux_vmcb;
	u32 cmd;

	u32 status = APP_SUCCESS;
	u32 ret = 0;

	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		cmd = (u32)r->eax;
		linux_vmcb = 0;
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
		cmd = (u32)linux_vmcb->rax;
	} else {
		printf("unknow cpu vendor type!\n");
		HALT();
	}

	switch (cmd)
	{
		case VMMCMD_TEST:
			{
				printf("\nCPU(0x%02x): Hello world from sechyp vmmcall handler!", vcpu->id);
				ret = 0;
				break;
			}
			/* register the scode */
		case VMMCMD_REG:
			{
				u32 scode_info, scode_sp, scode_pm, scode_en;
				/* sensitive code as guest virtual address in ecx */
				scode_info = r->ecx;
				/* sensitive code params information addres in esi */
				scode_pm = r->esi;
				/* sensitive code entry point in edi */
				scode_en = r->edi;

#ifdef __MP_VERSION__
				/* quiesce othe CPUs */
				g_isl->do_quiesce(vcpu);
#endif

				/* do atomic scode registration */
				ret = scode_register(vcpu, scode_info, scode_pm, scode_en);

#ifdef __MP_VERSION__
				/* wake up other CPUs */
				g_isl->do_wakeup(vcpu);
#endif
				break;
			}

			/* unregister the scode */
		case VMMCMD_UNREG:
			{
				u32 scode_gva;
				/* sensitive code as guest virtual address in ecx */
				scode_gva = r->ecx;

#ifdef __MP_VERSION__
				/* quiesce othe CPUs */
				g_isl->do_quiesce(vcpu);
#endif

				/* do atomic scode unregistration */
				ret = scode_unregister(vcpu, scode_gva);

#ifdef __MP_VERSION__
				/* wake up other CPUs */
				g_isl->do_wakeup(vcpu);
#endif
				break;
			}
			/* seal data */
		case VMMCMD_SEAL:
			{
				u32 inbuf, outbuf, data_addr, data_len, pcr_addr, out_addr, out_len_addr;
				inbuf = r->ecx;
				outbuf = r->esi;
				data_addr = get_32bit_aligned_value_from_guest(vcpu, inbuf); 
				data_len = get_32bit_aligned_value_from_guest(vcpu, inbuf+4);
				/* valid pcr value for unseal in edx */
				pcr_addr = r->edx;
				out_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf);
				out_len_addr = get_32bit_aligned_value_from_guest(vcpu,outbuf+4);

				ret = scode_seal(vcpu, data_addr, data_len, pcr_addr, out_addr, out_len_addr);

				break;
			}
			/* unseal data */
		case VMMCMD_UNSEAL:
			{
				u32 inbuf, outbuf, input_addr, in_len, out_addr, out_len_addr;
				inbuf = r->ecx;
				outbuf = r->edx;

				input_addr = get_32bit_aligned_value_from_guest(vcpu, inbuf);
				in_len = get_32bit_aligned_value_from_guest(vcpu, inbuf+4);
				out_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf);
				out_len_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf+4);

				ret = scode_unseal(vcpu, input_addr, in_len, out_addr, out_len_addr);

				break;
			}
		case VMMCMD_QUOTE:
			{
				u32 outbuf, nonce_addr, tpmsel_addr, out_addr, out_len_addr;
				/* address of nonce to be sealed in esi*/
				nonce_addr = r->esi;
				/* tpm selection data address in ecx */
				tpmsel_addr = r->ecx;

				outbuf = r->edx;
				out_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf);
				out_len_addr = get_32bit_aligned_value_from_guest(vcpu,outbuf+4);

				ret = scode_quote(vcpu,nonce_addr,tpmsel_addr,out_addr,out_len_addr);

				break;
			}
		case VMMCMD_SHARE:
			{
				u32 scode_entry, addrs_gva, lens_gva, count;
				u32 *addrs=NULL, *lens=NULL;

				scode_entry = r->ecx;

				addrs_gva = r->edx;
				lens_gva = r->esi;
				count = r->edi;

				addrs = vnmalloc(count, sizeof(u32));
				copy_from_guest(vcpu, (u8*)addrs, addrs_gva, sizeof(u32)*count);

				lens = vnmalloc(count, sizeof(u32));
				copy_from_guest(vcpu, (u8*)lens, lens_gva, sizeof(u32)*count);

				if (lens && addrs) {
					ret = scode_share_ranges(vcpu, scode_entry, addrs, lens, count);
				} else {
					printf("[TV] VMMCMD_SHARE: ERROR- couldn't allocate %d entries\n",
								 count);
					ret = -2;
				}

				vfree(addrs);
				vfree(lens);
				break;
			}
		default:
			{
				printf("[TV] FATAL ERROR: Invalid vmmcall cmd (%d)\n", cmd);
				status = APP_ERROR;
				ret = 1;
			}
	}

	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		r->eax = ret;
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		linux_vmcb->rax = ret;
	} else {
		printf("unknow cpu vendor type!\n");
		HALT();
	}
	return status;
}

/* EPT violation handler */
u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
		struct regs *r, u64 gpa, u64 gva, u64 violationcode)
{
	u32 ret;
	printf("\nCPU(0x%02x): gva=0x%08x, gpa=0x%08x, code=0x%08x\n", vcpu->id,
			(u32)gva, (u32)gpa, (u32)violationcode);
	ASSERT(tv_ctx != 0);
	//	printf("\nprot is: 0x%016llx", emhf_hwpgtbl_getprot(vcpu, gpa));
	if ((ret = tv_ctx->scode_npf(vcpu, gpa, (u32)violationcode)) != 0) {
		printf("FATAL ERROR: Unexpected return value from page fault handling\n");
		HALT();
	}
}

u32 emhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, 
		u32 portnum, u32 access_type, u32 access_size)
{
	printf("\nCPU(0x%02x): Port access intercept feature unimplemented. Halting!", vcpu->id);
	printf("\nCPU(0x%02x): portnum=0x%08x, access_type=0x%08x, access_size=0x%08x", vcpu->id,
			(u32)portnum, (u32)access_type, (u32)access_size);
	HALT();
	//return APP_IOINTERCEPT_SKIP;
	//return APP_IOINTERCEPT_CHAIN; //chain and do the required I/O    
}


void emhf_app_handleshutdown(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): Shutdown intercept!", vcpu->id);
	g_libemhf->emhf_reboot(vcpu);
}
