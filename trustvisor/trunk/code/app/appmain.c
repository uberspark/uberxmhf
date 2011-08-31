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

#include <target.h>
#include <puttymem.h>
#include <scode.h>
#include <globals.h>
#include <hc_utpm.h>
#include <nv.h>

/* Declared in linuxrelc.c.  TODO: figure out an approriate header
 * file for it. */
void setuplinuxboot(VCPU *vcpu, u32 vmlinuz_base, u32 vmlinuz_size, 
                    u32 initrd_base, u32 initrd_size);

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
		case TV_HC_TEST:
			{
				printf("\nCPU(0x%02x): Hello world from sechyp vmmcall handler!", vcpu->id);
				ret = 0;
				break;
			}
			/* register the scode */
		case TV_HC_REG:
			{
				u32 scode_info, /*scode_sp,*/ scode_pm, scode_en;
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
		case TV_HC_UNREG:
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
		case TV_HC_UTPM_SEAL_DEPRECATED:
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

				ret = hc_utpm_seal_deprecated(vcpu, data_addr, data_len, pcr_addr, out_addr, out_len_addr);

				break;
			}
			/* unseal data */
		case TV_HC_UTPM_UNSEAL:
		  {
				u32 inbuf, outbuf, input_addr, in_len, out_addr, out_len_addr, digestAtCreation_addr;
				inbuf = r->ecx;
				outbuf = r->edx;

				input_addr = get_32bit_aligned_value_from_guest(vcpu, inbuf);
				in_len = get_32bit_aligned_value_from_guest(vcpu, inbuf+4);
				out_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf);
				out_len_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf+4);
				digestAtCreation_addr = r->esi;				
				
				ret = hc_utpm_unseal(vcpu, input_addr, in_len, out_addr, out_len_addr, digestAtCreation_addr);
			}
      break;
		case TV_HC_UTPM_SEAL:
		  {
				u32 inbuf, outbuf, data_addr, data_len, pcrinfo_addr, out_addr, out_len_addr;
				inbuf = r->ecx;
				outbuf = r->esi;
				data_addr = get_32bit_aligned_value_from_guest(vcpu, inbuf); 
				data_len = get_32bit_aligned_value_from_guest(vcpu, inbuf+4);
				/* valid pcr value for unseal in edx */
				pcrinfo_addr = r->edx;
				out_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf);
				out_len_addr = get_32bit_aligned_value_from_guest(vcpu,outbuf+4);

				ret = hc_utpm_seal(vcpu, data_addr, data_len, pcrinfo_addr, out_addr, out_len_addr);
			}
			break;
		case TV_HC_UTPM_UNSEAL_DEPRECATED:
			{
				u32 inbuf, outbuf, input_addr, in_len, out_addr, out_len_addr;
				inbuf = r->ecx;
				outbuf = r->edx;

				input_addr = get_32bit_aligned_value_from_guest(vcpu, inbuf);
				in_len = get_32bit_aligned_value_from_guest(vcpu, inbuf+4);
				out_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf);
				out_len_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf+4);

				ret = hc_utpm_unseal_deprecated(vcpu, input_addr, in_len, out_addr, out_len_addr);

				break;
			}
		case TV_HC_UTPM_QUOTE:
		  {
				u32 sigbuf, nonce_addr, tpmsel_addr, sig_addr, sig_len_addr,
						pcrCompbuf, pcrComp_addr, pcrCompLen_addr;
        printf("[TV] TV_HC_UTPM_QUOTE hypercall received.\n");
				/* address of nonce to be sealed in esi*/
				nonce_addr = r->esi;
				/* tpm selection data address in ecx */
				tpmsel_addr = r->ecx;

				/* signature buffer and its length in array */
				sigbuf = r->edx;
				sig_addr = get_32bit_aligned_value_from_guest(vcpu, sigbuf);
				sig_len_addr = get_32bit_aligned_value_from_guest(vcpu,sigbuf+4);

				/* PCR Composite buffer and its length in array */
				pcrCompbuf = r->edi;
				pcrComp_addr = get_32bit_aligned_value_from_guest(vcpu, pcrCompbuf);
				pcrCompLen_addr = get_32bit_aligned_value_from_guest(vcpu, pcrCompbuf+4);
				
				ret = hc_utpm_quote(vcpu, nonce_addr, tpmsel_addr, sig_addr, sig_len_addr, pcrComp_addr, pcrCompLen_addr);

				break;
			}
    case TV_HC_UTPM_ID_GETPUB:
		  {
        u32 addr;
				addr = r->ecx;
				ret = hc_utpm_utpm_id_getpub(vcpu, addr);
				break;
			}
		case TV_HC_UTPM_QUOTE_DEPRECATED:
			{
				u32 outbuf, nonce_addr, tpmsel_addr, out_addr, out_len_addr;
				/* address of nonce to be sealed in esi*/
				nonce_addr = r->esi;
				/* tpm selection data address in ecx */
				tpmsel_addr = r->ecx;

				outbuf = r->edx;
				out_addr = get_32bit_aligned_value_from_guest(vcpu, outbuf);
				out_len_addr = get_32bit_aligned_value_from_guest(vcpu,outbuf+4);

				ret = hc_utpm_quote_deprecated(vcpu,nonce_addr,tpmsel_addr,out_addr,out_len_addr);

				break;
			}
		case TV_HC_SHARE:
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
					printf("[TV] TV_VMMCMD_SHARE: ERROR- couldn't allocate %d entries\n",
								 count);
					ret = -2;
				}

				vfree(addrs);
				vfree(lens);
				break;
			}
		case TV_HC_UTPM_PCRREAD:
			{
				u32 addr, num;
				addr = r->edx;
				num = r->ecx;
				ret = hc_utpm_pcrread(vcpu, addr, num);
				break;
			}
		case TV_HC_UTPM_PCREXT:
			{
				u32 meas_addr, idx;
				meas_addr = r->edx;
				idx = r->ecx;
				ret = hc_utpm_pcrextend(vcpu, idx, meas_addr);
				break;
			}
		case TV_HC_UTPM_GENRAND:
			{
				u32 addr, len_addr;
				addr = r->ecx;
				len_addr = r->edx;
				ret = hc_utpm_rand(vcpu, addr, len_addr);
				break;
			}
    case TV_HC_TPMNVRAM_GETSIZE:
		  {
				u32 size_addr;
				size_addr = r->ecx;
				ret = hc_tpmnvram_getsize(vcpu, size_addr);
				break;
			}
    case TV_HC_TPMNVRAM_READALL:
        {
						break;
        }
    case TV_HC_TPMNVRAM_WRITEALL:
        {
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
		struct regs __attribute__((unused)) *r, u64 gpa, u64 gva, u64 violationcode)
{
	u32 ret;
	dprintf(LOG_TRACE, "\nCPU(0x%02x): gva=0x%08Lx, gpa=0x%08Lx, code=0x%016Lx\n", (int)vcpu->id,
			gva, gpa, violationcode);
	//	printf("\nprot is: 0x%016llx", emhf_hwpgtbl_getprot(vcpu, gpa));
	if ((ret = hpt_scode_npf(vcpu, gpa, violationcode)) != 0) {
		dprintf(LOG_ERROR, "FATAL ERROR: Unexpected return value from page fault handling\n");
		HALT();
	}
    return ret;
}

u32 emhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs __attribute__((unused)) *r, 
		u32 portnum, u32 access_type, u32 access_size)
{
	dprintf(LOG_TRACE, "\nCPU(0x%02x): Port access intercept feature unimplemented. Halting!", vcpu->id);
	dprintf(LOG_TRACE, "\nCPU(0x%02x): portnum=0x%08x, access_type=0x%08x, access_size=0x%08x", vcpu->id,
			(u32)portnum, (u32)access_type, (u32)access_size);
	HALT();
    return 0; /* XXX DUMMY; keeps compiler happy */
	//return APP_IOINTERCEPT_SKIP;
	//return APP_IOINTERCEPT_CHAIN; //chain and do the required I/O    
}


void emhf_app_handleshutdown(VCPU *vcpu, struct regs __attribute__((unused)) *r)
{
	dprintf(LOG_TRACE, "\nCPU(0x%02x): Shutdown intercept!", vcpu->id);
	g_libemhf->emhf_reboot(vcpu);
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
