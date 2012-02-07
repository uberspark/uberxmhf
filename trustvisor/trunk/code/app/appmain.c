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

#include <emhf.h> 

#include <malloc.h>
#include <scode.h>
#include <hc_utpm.h>
#include <nv.h>

#include <tv_log.h>

/* Declared in linuxrelc.c.  TODO: figure out an approriate header
 * file for it. */
void setuplinuxboot(VCPU *vcpu, u32 vmlinuz_base, u32 vmlinuz_size, 
                    u32 initrd_base, u32 initrd_size);

// a placeholder for now...
u32 emhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb){
  eu_trace("CPU(0x%02x)", vcpu->id);

#ifdef __MP_VERSION__
  if (vcpu->isbsp) 
#endif
    {
      eu_trace("CPU(0x%02x): init\n", vcpu->id);
      init_scode(vcpu);

      //sanity checks
      //	ASSERT( apb->bootsector_size > 0 && apb->optionalmodule_size > 0 );

      if (apb->optionalmodule_ptr) {
        eu_trace("CPU(0x%02x): vmlinuz b=0x%08x, size=%u bytes", vcpu->id,
                 apb->bootsector_ptr, apb->bootsector_size);
        eu_trace("CPU(0x%02x): initramfs b=0x%08x, size=%u bytes", vcpu->id,
                 apb->optionalmodule_ptr, apb->optionalmodule_size);

        setuplinuxboot(vcpu, apb->bootsector_ptr, apb->bootsector_size, 
                       apb->optionalmodule_ptr, apb->optionalmodule_size);
      }

    }

  /* force these to be linked in */
  emhfc_log_error("");

  return APP_INIT_SUCCESS;  //successful
}

struct inbuf_s {
  u32 gva;
  u32 len;
};
struct outbuf_s {
  u32 gva;
  u32 len_gva;
};

static u32 do_TV_HC_SHARE(VCPU *vcpu, struct regs *r)
{
  u32 scode_entry, addrs_gva, lens_gva, count;
  u32 *addrs=NULL, *lens=NULL;
  u32 ret = 1;

  scode_entry = r->ecx;

  addrs_gva = r->edx;
  lens_gva = r->esi;
  count = r->edi;

  EU_CHK( addrs = malloc(count * sizeof(addrs[0])));
  EU_CHK( lens = malloc(count * sizeof(lens[0])));

  EU_CHKN( copy_from_current_guest( vcpu,
                                    addrs,
                                    addrs_gva,
                                    sizeof(addrs[0])*count));
  EU_CHKN( copy_from_current_guest( vcpu,
                                    lens,
                                    lens_gva,
                                    sizeof(lens[0])*count));

  ret = scode_share_ranges(vcpu, scode_entry, addrs, lens, count);

 out:
  free(addrs);
  free(lens);
  return ret;
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
        eu_trace("CPU(0x%02x): test hypercall", vcpu->id);
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
        emhf_smpguest_quiesce(vcpu);
#endif

        /* do atomic scode registration */
        ret = scode_register(vcpu, scode_info, scode_pm, scode_en);

#ifdef __MP_VERSION__
        /* wake up other CPUs */
        emhf_smpguest_endquiesce(vcpu);
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
        emhf_smpguest_quiesce(vcpu);
#endif

        /* do atomic scode unregistration */
        ret = scode_unregister(vcpu, scode_gva);

#ifdef __MP_VERSION__
        /* wake up other CPUs */
        emhf_smpguest_endquiesce(vcpu);
#endif
        break;
      }
      /* seal data */
    case TV_HC_UTPM_SEAL_DEPRECATED:
      {
        struct inbuf_s plainbuf_s;
        struct outbuf_s sealedbuf_s;
        gva_t plainbuf_s_gva;
        gva_t sealedbuf_s_gva;
        gva_t pcr_gva;

        plainbuf_s_gva = r->ecx;
        sealedbuf_s_gva = r->esi;
        pcr_gva = r->edx;        
        
        ret = 1;
        EU_CHKN( copy_from_current_guest( vcpu,
                                          &plainbuf_s,
                                          plainbuf_s_gva,
                                          sizeof(plainbuf_s)));

        EU_CHKN( copy_from_current_guest( vcpu,
                                          &sealedbuf_s,
                                          sealedbuf_s_gva,
                                          sizeof(sealedbuf_s)));

        ret = hc_utpm_seal_deprecated(vcpu,
                                      plainbuf_s.gva, plainbuf_s.len,
                                      pcr_gva,
                                      sealedbuf_s.gva, sealedbuf_s.len_gva);

        break;
      }
      /* unseal data */
    case TV_HC_UTPM_UNSEAL:
      {
        struct inbuf_s sealedbuf_s;
        struct outbuf_s plainbuf_s;
        gva_t sealedbuf_s_gva, plainbuf_s_gva;
        gva_t digestAtCreation_gva;

        sealedbuf_s_gva = r->ecx;
        plainbuf_s_gva = r->edx;
        digestAtCreation_gva = r->esi;				

        EU_CHKN( copy_from_current_guest( vcpu,
                                          &sealedbuf_s,
                                          sealedbuf_s_gva,
                                          sizeof(sealedbuf_s)));
        EU_CHKN( copy_from_current_guest( vcpu,
                                          &plainbuf_s,
                                          plainbuf_s_gva,
                                          sizeof(plainbuf_s)));
				
        ret = hc_utpm_unseal( vcpu,
                              sealedbuf_s.gva, sealedbuf_s.len,
                              plainbuf_s.gva, plainbuf_s.len_gva,
                              digestAtCreation_gva);
      }
      break;
    case TV_HC_UTPM_SEAL:
      {
        struct inbuf_s plainbuf_s;
        struct outbuf_s sealedbuf_s;
        gva_t sealedbuf_s_gva, plainbuf_s_gva;
        gva_t pcrinfo_gva;
        
        plainbuf_s_gva = r->ecx;
        sealedbuf_s_gva = r->esi;
        pcrinfo_gva = r->edx;

        ret = 1;
        EU_CHKN( copy_from_current_guest( vcpu,
                                          &plainbuf_s,
                                          plainbuf_s_gva,
                                          sizeof(plainbuf_s)));
        EU_CHKN( copy_from_current_guest( vcpu,
                                          &sealedbuf_s,
                                          sealedbuf_s_gva,
                                          sizeof(sealedbuf_s)));

        ret = hc_utpm_seal( vcpu,
                            plainbuf_s.gva, plainbuf_s.len,
                            pcrinfo_gva,
                            sealedbuf_s.gva, sealedbuf_s.len_gva);
      }
      break;
    case TV_HC_UTPM_UNSEAL_DEPRECATED:
      {
        struct inbuf_s sealedbuf_s;
        struct outbuf_s plainbuf_s;
        gva_t plainbuf_s_gva, sealedbuf_s_gva;

        sealedbuf_s_gva = r->ecx;
        plainbuf_s_gva = r->edx;

        EU_CHKN( copy_from_current_guest( vcpu,
                                          &sealedbuf_s,
                                          sealedbuf_s_gva,
                                          sizeof(sealedbuf_s)));

        EU_CHKN( copy_from_current_guest( vcpu,
                                          &plainbuf_s,
                                          plainbuf_s_gva,
                                          sizeof(plainbuf_s)));

        ret = hc_utpm_unseal_deprecated(vcpu,
                                        sealedbuf_s.gva, sealedbuf_s.len,
                                        plainbuf_s.gva, plainbuf_s.len_gva);

        break;
      }
    case TV_HC_UTPM_QUOTE:
      {
        gva_t nonce_gva, tpmsel_gva;
        struct outbuf_s sigbuf_s;
        gva_t sigbuf_s_gva;
        struct outbuf_s pcr_comp_buf_s;
        gva_t pcr_comp_buf_s_gva;

        eu_trace("TV_HC_UTPM_QUOTE hypercall received.");
        ret = 1;
        
        nonce_gva = r->esi; /* address of nonce to be sealed */
        tpmsel_gva = r->ecx; /* tpm selection data address */
        pcr_comp_buf_s_gva = r->edi; /* PCR Composite buffer and its length */
        sigbuf_s_gva = r->edx; /* signature buffer and its length */

        EU_CHKN( copy_from_current_guest( vcpu,
                                          &sigbuf_s,
                                          sigbuf_s_gva,
                                          sizeof(sigbuf_s)));
        
        EU_CHKN( copy_from_current_guest( vcpu,
                                          &pcr_comp_buf_s,
                                          pcr_comp_buf_s_gva,
                                          sizeof(sigbuf_s)));
				
        ret = hc_utpm_quote( vcpu,
                             nonce_gva,
                             tpmsel_gva,
                             sigbuf_s.gva, sigbuf_s.len_gva,
                             pcr_comp_buf_s.gva, pcr_comp_buf_s.len_gva);

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
        struct outbuf_s sigbuf_s;
        gva_t sigbuf_s_gva;
        gva_t nonce_gva, tpmsel_gva;

        ret = 1;
        
        nonce_gva = r->esi; /* address of nonce to be sealed */
        tpmsel_gva = r->ecx; /* tpm selection data address */
        sigbuf_s_gva = r->edx;

        EU_CHKN( copy_from_current_guest( vcpu,
                                          &sigbuf_s,
                                          sigbuf_s_gva,
                                          sizeof(sigbuf_s)));

        ret = hc_utpm_quote_deprecated( vcpu,
                                        nonce_gva,
                                        tpmsel_gva,
                                        sigbuf_s.gva, sigbuf_s.len_gva);

        break;
      }

    case TV_HC_SHARE:
      {
        ret = do_TV_HC_SHARE(vcpu, r);
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
        eu_trace("TV_HC_TPMNVRAM_GETSIZE invoked.");
        size_addr = r->ecx;
        ret = hc_tpmnvram_getsize(vcpu, size_addr);
        break;
      }
    case TV_HC_TPMNVRAM_READALL:
      {
        u32 out_addr;
        eu_trace("TV_HC_TPMNVRAM_READALL invoked.");
        out_addr = r->ecx;
        ret = hc_tpmnvram_readall(vcpu, out_addr);
        break;
      }
    case TV_HC_TPMNVRAM_WRITEALL:
      {
        u32 in_addr;
        eu_trace("TV_HC_TPMNVRAM_WRITEALL invoked.");
        in_addr = r->ecx;
        ret = hc_tpmnvram_writeall(vcpu, in_addr);
        break;
      }
    default:
      {
        eu_err("FATAL ERROR: Invalid vmmcall cmd (%d)", cmd);
        status = APP_ERROR;
        ret = 1;
      }
    }

 out:

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
  eu_trace("CPU(0x%02x): gva=0x%08Lx, gpa=0x%08Lx, code=0x%016Lx", (int)vcpu->id,
          gva, gpa, violationcode);
  //	printf("\nprot is: 0x%016llx", emhf_hwpgtbl_getprot(vcpu, gpa));
  if ((ret = hpt_scode_npf(vcpu, gpa, violationcode)) != 0) {
    eu_trace("FATAL ERROR: Unexpected return value from page fault handling");
    HALT();
  }
  return ret;
}

u32 emhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs __attribute__((unused)) *r, 
                                        u32 portnum, u32 access_type, u32 access_size)
{
  eu_err("CPU(0x%02x): Port access intercept feature unimplemented. Halting!", vcpu->id);
  eu_trace("CPU(0x%02x): portnum=0x%08x, access_type=0x%08x, access_size=0x%08x", vcpu->id,
           (u32)portnum, (u32)access_type, (u32)access_size);
  HALT();
  return 0; /* XXX DUMMY; keeps compiler happy */
  //return APP_IOINTERCEPT_SKIP;
  //return APP_IOINTERCEPT_CHAIN; //chain and do the required I/O    
}

void emhf_app_handleshutdown(VCPU *vcpu, struct regs __attribute__((unused)) *r)
{
  eu_trace("CPU(0x%02x): Shutdown intercept!", vcpu->id);
  //g_libemhf->emhf_reboot(vcpu);
  emhf_baseplatform_reboot(vcpu);
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:nil */
/* c-basic-offset:2 */
/* End:             */
