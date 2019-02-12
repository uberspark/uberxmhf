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

// XMHF/GEEC sentinel header file
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __GEEC_SENTINEL_H_
#define __GEEC_SENTINEL_H_


#define UAPI_SENTINEL_INSTALLSYSCALLSTUB     0
#define UAPI_SENTINEL_TEST    1


#ifndef __ASSEMBLY__


extern __attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) uint8_t _sysenter_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];

extern __attribute__((section(".data"))) __attribute__((aligned(4096))) xmhfgeec_slab_info_t xmhfgeec_slab_info_table[XMHFGEEC_TOTAL_SLABS];


typedef struct {
    uint32_t src_slabid;
    uint32_t dst_slabid;
    uint32_t slab_ctype;
    void *caller_stack_frame;
    slab_params_t *sp;
}__attribute__((packed)) gs_siss_element_t;


extern __attribute__((section(".data"))) uint32_t gs_siss_indices[MAX_PLATFORM_CPUS];
extern __attribute__((section(".data"))) gs_siss_element_t gs_siss[MAX_PLATFORM_CPUS][512];


//@	logic uint32_t sissCapacity{L}(uint32_t siss_id) = (uint32_t)512;

//@	logic uint32_t sissSize{L}(uint32_t siss_id) = gs_siss_indices[siss_id];

//@	logic gs_siss_element_t * sissStorage{L}(uint32_t siss_id) = &gs_siss[siss_id][0];

/*@
 predicate sissTop{L}(gs_siss_element_t * elem, integer index, gs_siss_element_t input) =
		(elem[index].src_slabid == input.src_slabid &&
		elem[index].dst_slabid == input.dst_slabid &&
		elem[index].slab_ctype == input.slab_ctype &&
		elem[index].caller_stack_frame == input.caller_stack_frame &&
		elem[index].sp == input.sp
		);
*/

//@	predicate sissEmpty{L}(uint32_t siss_id) = (sissSize(siss_id) == 0);

//@	predicate sissFull{L}(uint32_t siss_id) = (sissSize(siss_id) == sissCapacity(siss_id));

/*@
	predicate
	sissUnchanged {A,B } ( gs_siss_element_t * a, integer first, integer last ) =
	\forall integer i; first <= i < last
	==> ( (\at (a[i].src_slabid , A) == \at( a[i].src_slabid , B)) &&
		(\at (a[i].dst_slabid , A) == \at( a[i].dst_slabid , B)) &&
		(\at (a[i].slab_ctype , A) == \at( a[i].slab_ctype , B)) &&
		(\at (a[i].caller_stack_frame , A) == \at( a[i].caller_stack_frame , B)) &&
		(\at (a[i].sp , A) == \at( a[i].sp , B))
	);
*/

/*@
	predicate sissValid{L}(uint32_t siss_id) =
		(siss_id < MAX_PLATFORM_CPUS &&
		0 < sissCapacity( siss_id) &&
		0 <= sissSize (siss_id) <= sissCapacity ( siss_id) &&
		\valid (sissStorage (siss_id) + (0 .. sissCapacity (siss_id) - 1))
		);
@*/

//void gs_siss_pop(uint32_t cpuid, uint32_t *src_slabid, uint32_t *dst_slabid, uint32_t *hic_calltype,
                       //void **caller_stack_framep, slab_params_t **spp);

void gs_siss_pop(uint32_t siss_id, gs_siss_element_t *elem);
                       //void **caller_stack_framep, slab_params_t **spp);




/*@
	requires sissValid (siss_id);

	assigns gs_siss_indices[siss_id];
	assigns gs_siss[siss_id][gs_siss_indices[siss_id]];

	behavior not_full:
		assumes !sissFull(siss_id);

		assigns gs_siss_indices[siss_id];
		assigns gs_siss[siss_id][gs_siss_indices[siss_id]];

		ensures H:sissValid (siss_id);
		ensures I:sissSize (siss_id) == sissSize {Old}(siss_id) + 1;
		ensures K:sissUnchanged {Pre ,Here }(sissStorage (siss_id), 0, sissSize{Pre}(siss_id));
		ensures J:sissTop( sissStorage (siss_id), sissSize{Pre}(siss_id), elem);
		ensures !sissEmpty (siss_id);
		ensures sissStorage (siss_id) == sissStorage {Old }( siss_id) ;
		ensures sissCapacity ( siss_id) == sissCapacity { Old }(siss_id) ;

	behavior full :
		assumes sissFull ( siss_id);

		assigns \nothing;

		ensures sissValid (siss_id);
		ensures sissFull ( siss_id);
		ensures sissUnchanged {Pre ,Here }(sissStorage (siss_id ), 0, sissSize(siss_id));
		ensures sissSize ( siss_id ) == sissSize { Old }(siss_id) ;
		ensures sissStorage (siss_id ) == sissStorage {Old }( siss_id) ;
		ensures sissCapacity ( siss_id ) == sissCapacity { Old }(siss_id) ;

	complete behaviors ;
	disjoint behaviors ;
*/
void gs_siss_push(uint32_t siss_id, gs_siss_element_t elem);


void geec_sentinel_main(slab_params_t *sp, void *caller_stack_frame);




//void gs_entry_excp(x86vmx_exception_frame_t *exframe);
//CASM_FUNCDECL(void gs_exit_callexcp(uint32_t entry_point, void *caller_stack_frame));
//CASM_FUNCDECL(void gs_exit_retexcp(x86vmx_exception_frame_t *exframe));

CASM_FUNCDECL(void gs_calluobj(slab_params_t *sp, uint32_t entry_point));

CASM_FUNCDECL(void gs_syscallstub(void *noparam));
void gs_entry_syscall(slab_params_t *sp, void *caller_stack_frame);

void gs_exit_retv2uv(slab_params_t *sp, void *caller_stack_frame);
CASM_FUNCDECL(void gs_exit_retv2uvstub(void *caller_stack_frame));

void gs_exit_calluv2v(slab_params_t *sp, void *caller_stack_frame);
CASM_FUNCDECL(void gs_exit_calluv2vstub(uint32_t entry_point, void *callee_stack_frame));



void gs_exit_callv2uv(slab_params_t *sp, void *caller_stack_frame);
CASM_FUNCDECL(void gs_exit_callv2uvstub(uint32_t entry_point, void *callee_stack_frame));


void gs_exit_retuv2v(slab_params_t *sp, void *caller_stack_frame);
CASM_FUNCDECL(void gs_exit_retuv2vstub(void *caller_stack_frame));



CASM_FUNCDECL(void gs_exit_callv2v(uint32_t entry_point, void *caller_stack_frame));

CASM_FUNCDECL(void gs_exit_ret2v(void *caller_stack_frame));

CASM_FUNCDECL(uint32_t gs_exit_callv2uvg(void *noparam));




//CASM_FUNCDECL(void gs_entry_icptstub(void *noparam));
//void gs_entry_icpt(x86regs_t *r);
//CASM_FUNCDECL(void gs_exit_callicpt(uint32_t entry_point, void *caller_stack_frame));
//CASM_FUNCDECL(void gs_exit_reticpt(x86regs_t *r));



//CASM_FUNCDECL(void __xmhf_exception_handler_0(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_1(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_2(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_3(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_4(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_5(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_6(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_7(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_8(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_9(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_10(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_11(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_12(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_13(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_14(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_15(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_16(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_17(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_18(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_19(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_20(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_21(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_22(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_23(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_24(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_25(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_26(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_27(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_28(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_29(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_30(void *noparam));
//CASM_FUNCDECL(void __xmhf_exception_handler_31(void *noparam));







#endif // __ASSEMBLY__


#endif /* __GEEC_SENTINEL_H_ */
