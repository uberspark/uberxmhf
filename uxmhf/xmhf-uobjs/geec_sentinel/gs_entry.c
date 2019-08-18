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
 * HIC trampoline and stubs
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>
#include <xmhfgeec.h>
#include <geec_sentinel.h>

#include <uapi_iotbl.h>
#include <uapi_slabmempgtbl.h>


/////
// sentinel hub
/////

static inline void _geec_sentinel_checkandhalt_callcaps(uint32_t src_slabid, uint32_t dst_slabid, uint32_t dst_uapifn){
    //check call capabilities
    if( !(xmhfgeec_slab_info_table[dst_slabid].slab_callcaps & XMHFGEEC_SLAB_CALLCAP_MASK(src_slabid)) ){
        _XDPRINTF_("GEEC_SENTINEL: Halt!. callcap check failed for src(%u)-->dst(%u), dst caps=0x%x\n",
                   src_slabid, dst_slabid, xmhfgeec_slab_info_table[dst_slabid].slab_callcaps);
        HALT();
    }

    //check uapi capabilities
    if( xmhfgeec_slab_info_table[dst_slabid].slab_uapisupported){
        if(!(xmhfgeec_slab_info_table[src_slabid].slab_uapicaps[dst_slabid] & XMHFGEEC_SLAB_UAPICAP_MASK(dst_uapifn)))
        {
            _XDPRINTF_("GEEC_SENTINEL: Halt!. uapicap check failed for src(%u)-->dst(%u), dst_uapifn=%u, dst_uapimask=0x%08x\n",
                       src_slabid, dst_slabid, dst_uapifn,
                       (uint32_t)xmhfgeec_slab_info_table[src_slabid].slab_uapicaps[dst_slabid]);
            HALT();
        }
    }
}

//////
// process sentinel uobj specific calls
//////
void sentinel_processapicall(slab_params_t *sp, void *caller_stack_frame){
	//sanity check we are only being invoked by prime uobj
	if(sp->src_slabid != XMHFGEEC_SLAB_GEEC_PRIME){
		_XDPRINTF_("SENTINEL[ln:%u]: halting. should never be here!\n",
					   __LINE__);
		HALT();
	}

	switch(sp->dst_uapifn){
		case UAPI_SENTINEL_TEST:
		{
			slab_params_t spl;

			spl.slab_ctype = XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
			spl.src_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL;
			spl.dst_slabid = UOBJ_UAPI_IOTBL;
			spl.cpuid = sp->cpuid;
			spl.dst_uapifn = UXMHF_UAPI_IOTBL_TEST;

			CASM_FUNCCALL(gs_calluobj, &spl,
					xmhfgeec_slab_info_table[spl.dst_slabid].entrystub);

		}
		break;

		case UAPI_SENTINEL_INSTALLSYSCALLSTUB:
            _XDPRINTF_("SENTINEL[cpu=%u]: TEST\n",
                       (uint16_t)sp->cpuid);

            //setup SYSENTER/SYSEXIT mechanism
        	{
        	CASM_FUNCCALL(wrmsr64, IA32_SYSENTER_CS_MSR, (uint32_t)__CS_CPL0, 0);
        	CASM_FUNCCALL(wrmsr64, IA32_SYSENTER_EIP_MSR,
        			(uint32_t)&gs_syscallstub, 0);
        	CASM_FUNCCALL(wrmsr64, IA32_SYSENTER_ESP_MSR,
        			(uint32_t)((uint32_t)_sysenter_stack[(uint16_t)sp->cpuid] + MAX_PLATFORM_CPUSTACK_SIZE), 0);
        	}
        	_XDPRINTF_("%s: setup SYSENTER/SYSEXIT mechanism\n", __func__);
        	_XDPRINTF_("SYSENTER CS=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_CS_MSR));
        	_XDPRINTF_("SYSENTER RIP=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_EIP_MSR));
        	_XDPRINTF_("SYSENTER RSP=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_ESP_MSR));

            break;

		default:
			_XDPRINTF_("SENTINEL(ln:%u): Unrecognized transition. Halting!\n", __LINE__);
			HALT();
	}

	CASM_FUNCCALL(gs_exit_ret2v,
				  caller_stack_frame);

    _XDPRINTF_("SENTINEL[ln:%u]: halting. should never be here!\n",
               __LINE__);
    HALT();

}

void geec_sentinel_main(slab_params_t *sp, void *caller_stack_frame){



    switch(sp->slab_ctype){
        case XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG:{

        	if(sp->dst_slabid == XMHFGEEC_SLAB_GEEC_SENTINEL){
        		//this is a sentinel uobj specific initialization call
        		sentinel_processapicall(sp, caller_stack_frame);
        	}else{

				switch (xmhfgeec_slab_info_table[sp->dst_slabid].slabtype){

					case XMHFGEEC_SLABTYPE_VfT_PROG:{
						//_geec_sentinel_checkandhalt_callcaps(sp->src_slabid, sp->dst_slabid, sp->dst_uapifn);
						CASM_FUNCCALL(gs_exit_callv2v,
									  xmhfgeec_slab_info_table[sp->dst_slabid].entrystub,
									  caller_stack_frame);
						_XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
								   __LINE__);
						HALT();

					}
					break;


					case XMHFGEEC_SLABTYPE_uVT_PROG:
					case XMHFGEEC_SLABTYPE_uVU_PROG:{
						//_geec_sentinel_checkandhalt_callcaps(sp->src_slabid, sp->dst_slabid, sp->dst_uapifn);
						sp->slab_ctype = XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG;
						gs_exit_callv2uv(sp, caller_stack_frame);
						_XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
								   __LINE__);
						HALT();

					}
					break;


					case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
					case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
					case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
						uint32_t errorcode;
						//_geec_sentinel_checkandhalt_callcaps(sp->src_slabid, sp->dst_slabid, sp->dst_uapifn);
						//_XDPRINTF_("GEEC_SENTINEL: launching guest %u...\n", sp->dst_slabid);
						sp->slab_ctype = XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG_GUEST;
						CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VPID, sp->dst_slabid );

						{
							slab_params_t spl;
							uapi_ugmpgtbl_getmpgtblbase_params_t *ps = (uapi_ugmpgtbl_getmpgtblbase_params_t *)spl.in_out_params;

							spl.slab_ctype = XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
							spl.src_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL;
							spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
							spl.cpuid = sp->cpuid;
							spl.dst_uapifn = UAPI_UGMPGTBL_GETMPGTBLBASE;

							ps->dst_slabid = sp->dst_slabid;

							//_XDPRINTF_("GEEC_SENTINEL: guest: slabid=%u\n", ps->dst_slabid);

							CASM_FUNCCALL(gs_calluobj, &spl,
									xmhfgeec_slab_info_table[spl.dst_slabid].entrystub);

							//_XDPRINTF_("GEEC_SENTINEL: guest: eptp base=0x%08x\n", ps->mpgtblbase);

							CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, (ps->mpgtblbase  | 0x1E) );
							CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_HIGH, 0);
						}




						{
							slab_params_t spl;
							uapi_iotbl_getiotblbase_t *ps = (uapi_iotbl_getiotblbase_t *)spl.in_out_params;

							spl.slab_ctype = XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
							spl.src_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL;
							spl.dst_slabid = UOBJ_UAPI_IOTBL;
							spl.cpuid = sp->cpuid;
							spl.dst_uapifn = UXMHF_UAPI_IOTBL_GETIOTBLBASE;

							ps->dst_slabid = sp->dst_slabid;

							//_XDPRINTF_("GEEC_SENTINEL: guest: slabid=%u\n", ps->dst_slabid);

							CASM_FUNCCALL(gs_calluobj, &spl,
									xmhfgeec_slab_info_table[spl.dst_slabid].entrystub);

							//_XDPRINTF_("GEEC_SENTINEL: guest: iotbl_base=0x%08x\n", ps->iotbl_base);

							CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL, ps->iotbl_base);
							CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH, 0);
							CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL, (ps->iotbl_base + PAGE_SIZE_4K));
							CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH, 0);
						}

						if (xmhfgeec_slab_info_table[sp->dst_slabid].slabtype != XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST){
							CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RSP, xmhfgeec_slab_info_table[sp->dst_slabid].slabtos[(uint16_t)sp->cpuid]);
							CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RIP, xmhfgeec_slab_info_table[sp->dst_slabid].entrystub);
						}

						errorcode = CASM_FUNCCALL(gs_exit_callv2uvg, CASM_NOPARAM);

						switch(errorcode){
							case 0:	//no error code, VMCS pointer is invalid
								_XDPRINTF_("GEEC_SENTINEL: VMLAUNCH error; VMCS pointer invalid?\n");
								break;
							case 1:{//error code available, so dump it
								uint32_t code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
								_XDPRINTF_("GEEC_SENTINEL: VMLAUNCH error; code=%x\n", code);
								break;
							}
						}

						HALT();

					}
					break;

					default:
						_XDPRINTF_("GEEC_SENTINEL(ln:%u): Unrecognized transition. Halting!\n", __LINE__);
						HALT();
				}
        	} //endif

        }
        break;




        case XMHFGEEC_SENTINEL_RET_VfT_PROG_TO_uVT_uVU_PROG:{
                    gs_exit_retv2uv(sp, caller_stack_frame);
                    _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                               __LINE__);
                    HALT();
        }
        break;





        case XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG:{
            _geec_sentinel_checkandhalt_callcaps(sp->src_slabid, sp->dst_slabid, sp->dst_uapifn);
            gs_exit_calluv2v(sp, caller_stack_frame);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n", __LINE__);
            HALT();
        }
        break;




        case XMHFGEEC_SENTINEL_RET_uVT_uVU_PROG_TO_VfT_PROG:{
            gs_exit_retuv2v(sp, caller_stack_frame);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n", __LINE__);
            HALT();
        }
        break;


























        default:
            _XDPRINTF_("GEEC_SENTINEL: unkown call type %x. Halting!\n", sp->slab_ctype);
            HALT();

    }

}


