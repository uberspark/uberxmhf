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

//emhf.h - main EMHF core header file 
// this orchestrates the inclusion of other core component specific
// headers
//author: amit vasudevan (amitvasudevan@acm.org)
//
#ifndef __EMHF_H_
#define __EMHF_H_

//---includes for the target----------------------------------------------------
#ifndef __ASSEMBLY__
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#endif /* __ASSEMBLY__ */

#ifndef __ASSEMBLY__
#define BAD_INTEGRITY_HASH "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

/* SHA-1 hash of runtime should be defined during build process.
 * However, if it's not, don't fail.  Just proceed with all zeros.
 * XXX TODO Disable proceeding with insecure hash value. */
#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___RUNTIME_INTEGRITY_HASH___ */

//"golden" digest values injected using CFLAGS during build process
//NOTE: NO WAY TO SELF-CHECK slbelow64K; JUST A SANITY-CHECK
typedef struct _integrity_measurement_values {
    u8 sha_slbelow64K[20]; // TODO: play nice with SHA_DIGEST_LENGTH in sha1.h
    u8 sha_slabove64K[20];
    u8 sha_runtime[20];
} INTEGRITY_MEASUREMENT_VALUES;
#endif /* __ASSEMBLY__ */


#include <_ctype.h>		//the ctype variable definition for debug printf
#include <_com.h>		//serial UART as debugging backend
//#include <_print.h>      //early chance to disable/enable debug printfs
#include <_multiboot.h>  //boot manager (multiboot)
#include <_cmdline.h>	//GRUB command line handling functions
#include <_error.h>      //error handling and assertions

#include <_processor.h>  //CPU
#include <_msr.h>        //model specific registers
#include <_paging.h>     //MMU
#include <_io.h>         //legacy I/O
#include <_apic.h>       //APIC
#include <_svm.h>        //SVM extensions
#include <_vmx.h>				//VMX extensions

#include <_txt.h>		//Trusted eXecution Technology (SENTER support)

#include <_pci.h>        //PCI bus glue
#include <_acpi.h>				//ACPI glue

#include <_svm_eap.h>		//SVM DMA protection
#include <_vmx_eap.h>		//VMX DMA protection

#include <_tpm.h>			//generic TPM functions
#include <_tpm_emhf.h>		//EMHF-specific TPM functions

//language specifics
#include <_sarg.h>
#include <_div64.h>

#include <_perf.h>			//performance measurement routines



#include <emhf-types.h>		//EMHF specific base types

//----------------------------------------------------------------------
// component headers
#include <emhf-debug.h>		//EMHF debug component
#include <emhf-sl.h>		//EMHF secure loader component
#include <emhf-memprot.h>	//EMHF memory protection component
#include <emhf-dmaprot.h>	//EMHF DMA protection component
#include <emhf-parteventhub.h>	//EMHF partition event-hub component
#include <emhf-smpguest.h>		//EMHF SMP guest component
#include <emhf-xcphandler.h>	//EMHF exception handler component
#include <emhf-baseplatform.h>	//EMHF base platform component




#ifndef __ASSEMBLY__
//----------------------------------------------------------------------
// host to guest, guest to host VA to PA helpers
// XXX: should belong in the "platform" component
/* defined in global.h. can't just include globals.h because it
   depends on this header */
static inline void* spa2hva(spa_t spa);
static inline spa_t hva2spa(void *hva);
static inline spa_t gpa2spa(gpa_t gpa);
static inline gpa_t spa2gpa(spa_t spa);
static inline void* gpa2hva(gpa_t gpa);
static inline gpa_t hva2gpa(hva_t hva);

static inline u64 VCPU_gdtr_base(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_GDTR_base;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->gdtr.base;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline size_t VCPU_gdtr_limit(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_GDTR_limit;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->gdtr.limit;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline u64 VCPU_grflags(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RFLAGS;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rflags;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline void VCPU_grflags_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RFLAGS = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rflags = val;
  } else {
    ASSERT(false);
  }
}

static inline u64 VCPU_grip(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RIP;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rip;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline void VCPU_grip_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RIP = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rip = val;
  } else {
    ASSERT(false);
  }
}

static inline u64 VCPU_grsp(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RSP;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rsp;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline void VCPU_grsp_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RSP = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rsp = val;
  } else {
    ASSERT(false);
  }
}

static inline u64 VCPU_gcr3(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return vcpu->vmcs.guest_CR3;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->cr3;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline void VCPU_gcr3_set(VCPU *vcpu, u64 cr3)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    vcpu->vmcs.guest_CR3 = cr3;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->cr3 = cr3;
  } else {
    ASSERT(false);
  }
}

static inline u64 VCPU_gcr4(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return vcpu->vmcs.guest_CR4;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->cr4;
  } else {
    ASSERT(false);
    return 0;
  }
}

#include <_globals.h>

#endif

#endif /* __EMHF_H_ */
