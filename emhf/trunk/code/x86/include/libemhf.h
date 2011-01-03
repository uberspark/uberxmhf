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

// libemhf.h - EMHF application interface declarations  
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __LIBEMHF_H__
#define __LIBEMHF_H__

//generic catch-all app return codes
#define APP_SUCCESS     (0x1)
#define APP_ERROR				(0x0)

//h/w pagetable protection flags
#define HWPGTBL_FLAG_READ     ((u64)0x1 << 0)
#define HWPGTBL_FLAG_WRITE    ((u64)0x1 << 1)
#define HWPGTBL_FLAG_EXECUTE  ((u64)0x1 << 2)


#ifndef __ASSEMBLY__
//application parameter block
//for now it holds the bootsector and optional module info loaded by GRUB
//eventually this will be generic enough for both boot-time and dynamic loading
//capabilities
typedef struct {
  u32 bootsector_ptr;
  u32 bootsector_size;
  u32 optionalmodule_ptr;
  u32 optionalmodule_size;
  u32 runtimephysmembase;
} __attribute__((packed)) APP_PARAM_BLOCK;

//generic EMHF library interface
//note: VMX and SVM backends can have different implementations of these 
//interfaces
struct emhf_library {
	void 	(*emhf_iopm_set_write)(VCPU *vcpu, u32 port, u32 size);
	void 	(*emhf_msrpm_set_write)(VCPU *vcpu, u32 msr);
	void 	(*emhf_hwpgtbl_flushall)(VCPU *vcpu);
	void 	(*emhf_hwpgtbl_setprot)(VCPU *vcpu, u64 gpa, u64 flags);
	u64 	(*emhf_hwpgtbl_getprot)(VCPU *vcpu, u64 gpa);
	void 	(*emhf_hwpgtbl_setentry)(VCPU *vcpu, u64 gpa, u64 value);
	u32 	(*emhf_guestpgtbl_walk)(VCPU *vcpu, u32 gva);
	void 	(*emhf_reboot)(VCPU *vcpu);
}; 

//exported functions
void emhf_iopm_set_write(VCPU *vcpu, u32 port, u32 size);
void emhf_msrpm_set_write(VCPU *vcpu, u32 msr);
void emhf_hwpgtbl_flushall(VCPU *vcpu);
void emhf_hwpgtbl_setprot(VCPU *vcpu, u64 gpa, u64 flags);
u64 emhf_hwpgtbl_getprot(VCPU *vcpu, u64 gpa);
void emhf_hwpgtbl_setentry(VCPU *vcpu, u64 gpa, u64 value);
u32 emhf_guestpgtbl_walk(VCPU *vcpu, u32 gva);
void emhf_reboot(VCPU *vcpu);

//callbacks
extern u32 emhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb);
extern u32 emhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, u32 portnum, u32 access_type, u32 access_size); 
extern u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
      struct regs *r,
      u64 gpa, u64 gva, u64 violationcode);
extern void emhf_app_handleshutdown(VCPU *vcpu, struct regs *r);
extern u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r);	//returns APP_SUCCESS if handled, else APP_ERROR      

#endif //#ifndef __ASSEMBLY__


#endif // __LIBEMHF_H__ 

