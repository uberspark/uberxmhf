/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org), ethan joseph (ethanj217@gmail.com)
*/
#include <uberspark/include/uberspark.h>
#include <uberspark/hwm/include/arch/arm/hwm.h>


//r0, r1 and r2 are set by the boot-loader and need to
//be preserved
//.section ".uobj_pm_entry"

CASM_FUNCDEF(void, entry,
{
    __casm__mrc_p15_0_r3_c0_c0_5();	//read MPIDR
	__casm__and_imm_r3_r3(3);		//mask off the CPUID value
	__casm__add_imm_r4_r3(1);		//r4 = index into cpu_stacks

	__casm__ldr_pseudo_sp(cpu_stacks);	//load cpu_stacks base into stack-pointer
	__casm__mov_imm_r5(8192);
	__casm__mul_r6_r4_r5();	//r6 is the offset to add based on index (r4)
	__casm__add_sp_sp_r6();	//sp is the top-of-stack for this cpu
	__casm__bl(main);
}, void *noparam)

CASM_FUNCDEF(void, halt,
{
	__casm__b(halt);
}, void *noparam)

//r0,r1,r2 go through to the guest os
//r3 contains the starting address to execute the guestos
//clobbers r7,r9
CASM_FUNCDEF(void, chainload_os,
{
	__casm__mov_imm_r7(0);
	//mcr	p15, 4, r7, c1, c1, 0	// HCR=0
	__casm__mcr_p15_4_r7_c1_c1_2();	// HCPTR=0
	//mcr	p15, 4, r7, c1, c1, 3	// HSTR=0

	//mcr	p15, 4, r7, c1, c0, 0	// HSCTLR=0

	__casm__mrc_p15_4_r7_c1_c1_1();	// HDCR
	_impl__casm__and_imm_r7_r7(0x1f);				// Preserve HPMN
	__casm__mcr_p15_4_r7_c1_c1_1();	// HDCR


	// make CNTP_* and CNTPCT accessible from guest
	__casm__mrc_p15_0_r7_c0_c1_1(); // ID_PFR1
	__casm__lsr_imm_r7_r7(16);
	__casm__and_imm_r7_r7(0xf);
	__casm__cmp_imm_r7_r7(1);
	__casm__b_ne(1f);
	__casm__mrc_p15_4_r7_c14_c1_0(); // CNTHCTL
	__casm__orr_imm_r7_r7(3);    // PL1PCEN | PL1PCTEN
	__casm__mcr_p15_4_r7_c14_c1_0(); // CNTHCTL
	_impl__casm__mov_imm_r7(0);
	__casm__mcrr_p15_4_r7_r7_c14(); // CNTVOFF

	//disable virtual timer
	__casm__mrc_p15_0_r7_c14_c3_1(); // CNTV_CTL
	__casm_bic_imm_r7_r7(1);     // Clear ENABLE
	__casm__mcr_p15_0_r7_c14_c3_1(); // CNTV_CTL

CASM_LABEL(1);

	__casm__mrs_r9_cpsr();
	__casm__eor_imm_r9_r9(0x0000001a);  //HYP_MODE
	__casm__tst_imm_r9(0x0000001f);   //MODE_MASK
	__casm_bic_imm_r9_r9(0x0000001f); //MODE_MASK
	__casm__orr_imm_r9_r9(0x00000080 | 0x00000040 | 0x00000013); //PSR_I_BIT | PSR_F_BIT | SVC_MODE
	__casm__orr_imm_r9_r9(0x00000100)  //PSR_A_BIT
	__casm__msr_spsrcxsf_r9();
	__casm__msr_elrhyp_r3();   //store address to begin execution in SVC mode in ELR_hyp
	__casm__eret();
}, u32 r0, u32 id, struct atag *at, u32 address)

CASM_FUNCDEF(void, secondary_cpu_entry,
{
	__casm__mrc_p15_0_r0_c0_c0_5(); 	//read MPIDR
 	__casm__and_imm_r0_r0(3);						//mask off the CPUID value
	__casm__add_imm_r1_r0(1);					//r1 = index into cpu_stacks

	__casm__ldr_pseudo_sp(cpu_stacks);				//load cpu_stacks base into stack-pointer
	__casm__mov_imm_r2(8192);
	__casm__mul_r3_r2_r1();				//r3 is the offset to add based on index (r1)
	__casm__add_sp_sp_r3();			//sp is the top-of-stack for this cpu

	__casm__bl(secondary_main);				//r0 is the cpuid
}, void *noparam)

CASM_FUNCDEF(void, secondary_cpu_entry_halt,
{
	__casm__b(secondary_cpu_entry_halt);
}, void *noparam)


__attribute__((section(".stack")))
__attribute__((section("aw")))

__attribute__((aligned(8))) cpu_stacks[8192 * 4];

__attribute__((aligned(8))) cpu_stacks_svc[8192 * 4];

