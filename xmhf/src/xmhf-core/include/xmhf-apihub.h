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
 * 	xmhf-apihub.h
 * 
 *  XMHF core API interface component declarations/definitions
 * 
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __XMHF_APIHUB_H__
#define __XMHF_APIHUB_H__

//hypapp callbacks
#define XMHF_APIHUB_HYPAPPCB_MAIN					(0)
#define XMHF_APIHUB_HYPAPPCB_HYPERCALL				(1)
#define XMHF_APIHUB_HYPAPPCB_SHUTDOWN				(2)
#define XMHF_APIHUB_HYPAPPCB_HWPGTBLVIOLATION		(3)
#define XMHF_APIHUB_HYPAPPCB_PORTACCESS				(4)

//core APIs
#define	XMHF_APIHUB_COREAPI_OUTPUTDEBUGSTRING		(0)
#define XMHF_APIHUB_COREAPI_REBOOT					(1)
#define XMHF_APIHUB_COREAPI_SETMEMPROT				(2)
#define XMHF_APIHUB_COREAPI_MEMPROT_GETPROT			(3)
#define XMHF_APIHUB_COREAPI_MEMPROT_FLUSHMAPPINGS	(4)
#define XMHF_APIHUB_COREAPI_SMPGUEST_WALK_PAGETABLES	(5)
//#define XMHF_APIHUB_COREAPI_PARTITION_LEGACYIO_SETPROT 	(6)
//#define XMHF_APIHUB_COREAPI_BASEPLATFORM_ARCH_X86_ACPI_GETRSDP 	(7)

//#define XMHF_APIHUB_COREAPI_TPM_OPEN_LOCALITY		(8)
//#define XMHF_APIHUB_COREAPI_TPM_DEACTIVATE_ALL_LOCALITIES	(9)
//#define XMHF_APIHUB_COREAPI_TPM_WRITE_CMD_FIFO		(10)

//#define XMHF_APIHUB_COREAPI_MEMPROT_ARCH_X86SVM_GET_H_CR3	(11)
//#define XMHF_APIHUB_COREAPI_MEMPROT_ARCH_X86SVM_SET_H_CR3	(12)
//#define XMHF_APIHUB_COREAPI_MEMPROT_ARCH_X86VMX_GET_EPTP	(13)
//#define XMHF_APIHUB_COREAPI_MEMPROT_ARCH_X86VMX_SET_EPTP	(14)

#define XMHF_APIHUB_COREAPI_BASEPLATFORM_GETCPUTABLE		(15)
#define XMHF_APIHUB_COREAPI_MEMPROT_SETSINGULARHPT			(16)
#define XMHF_APIHUB_COREAPI_MEMPROT_GETHPTROOT			(17)

#define XMHF_APIHUB_COREAPI_HPT_SETENTRY					(18)

#define XMHF_APIHUB_COREAPI_HYPAPPCBRETURN					(0xFFFF)


#ifndef __ASSEMBLY__

//hypapp parameter block
typedef struct {
	u64 param1;
	u64 param2;
	u64 param3;
	u64 param4;
	u64 param5;
	u64 param6;
	u64 param7;
	u64 param8;
	u64 result;
	VCPU vcpu;
	//APP_PARAM_BLOCK apb;
	context_desc_t context_desc;
	hypapp_env_block_t hypappenvb;
	struct regs r;
	xmhfcoreapiretval_t retval;
} __attribute__((packed)) XMHF_HYPAPP_PARAMETERBLOCK;


#if !(defined __XMHF_CORE_APIHUB_SWFP__)

// declare paramcore and paramhypapp variables (which are defined in
// (runtime.lds.S)
extern u8 paramcore_start[];
extern u8 paramhypapp_start[];

// declare core and hypapp parameter blocks which are initialized over
// the above two memory regions
extern XMHF_HYPAPP_PARAMETERBLOCK *paramcore;
extern XMHF_HYPAPP_PARAMETERBLOCK *paramhypapp;

// hypapp PAE page tables
extern u64 hypapp_3level_pdpt[] __attribute__(( section(".palign_data") ));
extern u64 hypapp_3level_pdt[] __attribute__(( section(".palign_data") ));

//core PAE page tables
extern u64 core_3level_pdpt[] __attribute__(( section(".palign_data") ));
extern u64 core_3level_pdt[] __attribute__(( section(".palign_data") ));



void xmhfcore_outputdebugstring(const char *s);
void xmhfcore_reboot(context_desc_t context_desc);
//void xmhfcore_setmemprot(VCPU *vcpu, u64 gpa, u32 prottype);
void xmhfcore_setmemprot(context_desc_t context_desc, u64 gpa, u32 prottype);
//u32 xmhfcore_memprot_getprot(VCPU *vcpu, u64 gpa);
void xmhfcore_memprot_flushmappings(context_desc_t context_desc);
u8 * xmhfcore_smpguest_walk_pagetables(context_desc_t context_desc, u32 vaddr);
//void xmhfcore_partition_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype);

//int xmhfcore_tpm_open_locality(int locality);
//void xmhfcore_tpm_deactivate_all_localities(void);

//u64 xmhfcore_memprot_arch_x86svm_get_h_cr3(VCPU *vcpu);
//void xmhfcore_memprot_arch_x86svm_set_h_cr3(VCPU *vcpu, u64 n_cr3);
//u64 xmhfcore_memprot_arch_x86vmx_get_EPTP(VCPU *vcpu);
//void xmhfcore_memprot_arch_x86vmx_set_EPTP(VCPU *vcpu, u64 eptp);

//xmhfcoreapiretval_t xmhfcore_baseplatform_getcputable(void);
void xmhfcore_memprot_setsingularhpt(u64 hpt);
u64 xmhfcore_memprot_getHPTroot(context_desc_t context_desc);
void xmhfcore_memprot_hpt_setentry(context_desc_t context_desc, u64 hpt_paddr, u64 entry);
//uint32_t xmhfcore_tpm_write_cmd_fifo(uint32_t locality, uint8_t *in,
//                                   uint32_t in_size, uint8_t *out,
//                                   uint32_t *out_size);
//u32 xmhfcore_baseplatform_arch_x86_acpi_getRSDP(ACPI_RSDP *rsdp);


#else //SWFP

typedef void (*COREAPIXMHFCPUTS)(const char *s);
typedef void (*COREAPIXMHFBASEPLATFORMREBOOT)(VCPU *vcpu);
typedef void (*COREAPIXMHFSETMEMPROT)(VCPU *vcpu, u64 gpa, u32 prottype);
typedef u32 (*COREAPIXMHFMEMPROTGETPROT)(VCPU *vcpu, u64 gpa);
typedef void (*COREAPIXMHFMEMPROTFLUSHMAPPINGS)(VCPU *vcpu);
typedef u8 * (*COREAPIXMHFSMPGUESTWALKPAGETABLES)(VCPU *vcpu, u32 vaddr);
typedef void (*COREAPIXMHFPARTITIONLEGACYIOSETPROT)(VCPU *vcpu, u32 port, u32 size, u32 prottype);
typedef u32 (*COREAPIXMHFBASEPLATFORMARCHX86ACPIGETRSDP)(ACPI_RSDP *rsdp);

typedef int (*COREAPIXMHFTPMOPENLOCALITY)(int locality);
typedef void (*COREAPIXMHFTPMDEACTIVATEALLLOCALITIES)(void);
typedef uint32_t (*COREAPIXMHFTPMWRITECMDFIFO)(uint32_t locality, uint8_t *in,
                                   uint32_t in_size, uint8_t *out,
                                   uint32_t *out_size);

typedef u64 (*COREAPIXMHFMEMPROTARCHX86SVMGETHCR3)(VCPU *vcpu);
typedef void (*COREAPIXMHFMEMPROTARCHX86SVMSETHCR3)(VCPU *vcpu, u64 n_cr3);
typedef u64 (*COREAPIXMHFMEMPROTARCHX86VMXGETEPTP)(VCPU *vcpu);
typedef void (*COREAPIXMHFMEMPROTARCHX86VMXSETEPTP)(VCPU *vcpu, u64 eptp);

//typedef u32 (*COREAPIXMHFBASEPLATFORMGETCPUTABLE)(void *buffer, u32 sizeofbuffer);


extern COREAPIXMHFCPUTS xmhfcore_outputdebugstring;
extern COREAPIXMHFBASEPLATFORMREBOOT xmhfcore_reboot;
extern COREAPIXMHFSETMEMPROT xmhfcore_setmemprot;
extern COREAPIXMHFMEMPROTGETPROT xmhfcore_memprot_getprot;
extern COREAPIXMHFMEMPROTFLUSHMAPPINGS xmhfcore_memprot_flushmappings;
extern COREAPIXMHFSMPGUESTWALKPAGETABLES xmhfcore_smpguest_walk_pagetables;
extern COREAPIXMHFPARTITIONLEGACYIOSETPROT xmhfcore_partition_legacyIO_setprot;
extern COREAPIXMHFBASEPLATFORMARCHX86ACPIGETRSDP xmhfcore_baseplatform_arch_x86_acpi_getRSDP;

extern COREAPIXMHFTPMOPENLOCALITY xmhfcore_tpm_open_locality;
extern COREAPIXMHFTPMDEACTIVATEALLLOCALITIES xmhfcore_tpm_deactivate_all_localities;
extern COREAPIXMHFTPMWRITECMDFIFO xmhfcore_tpm_write_cmd_fifo;

extern COREAPIXMHFMEMPROTARCHX86SVMGETHCR3 xmhfcore_memprot_arch_x86svm_get_h_cr3;
extern COREAPIXMHFMEMPROTARCHX86SVMSETHCR3 xmhfcore_memprot_arch_x86svm_set_h_cr3;
extern COREAPIXMHFMEMPROTARCHX86VMXGETEPTP xmhfcore_memprot_arch_x86vmx_get_EPTP;
extern COREAPIXMHFMEMPROTARCHX86VMXSETEPTP xmhfcore_memprot_arch_x86vmx_set_EPTP;

//extern COREAPIXMHFBASEPLATFORMGETCPUTABLE xmhfcore_baseplatform_getcputable;
#endif


//----------------------------------------------------------------------
//exported DATA 
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------
void xmhf_apihub_initialize (void);


//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------
void xmhf_apihub_arch_initialize(void);
void xmhf_apihub_arch_tohypapp(u32 hypappcallnum);

//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//x86svm SUBARCH. INTERFACES
//----------------------------------------------------------------------



#endif	//__ASSEMBLY__

#endif //__XMHF_APIHUB_H__
