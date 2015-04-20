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

#include <xc.h>
#include <geec_sentinel.h>
#include <geec_primesmp.h> //TODO: we rely on this only for cpuidtable, need to eliminate


#if 0
__attribute__((section(".data"))) u64 __xmhfhic_safestack_indices[MAX_PLATFORM_CPUS] = { 0 };

__attribute__((section(".data"))) __xmhfhic_safestack_element_t __xmhfhic_safestack[MAX_PLATFORM_CPUS][512];



bool __xmhfhic_callcaps(u64 src_slabid, u64 dst_slabid){
    if( _xmhfhic_common_slab_info_table[src_slabid].slab_callcaps & HIC_SLAB_CALLCAP(dst_slabid))
        return true;
    else
        return false;
}


void __xmhfhic_safepush(u64 cpuid, u64 src_slabid, u64 dst_slabid, u64 hic_calltype, u64 return_address,
                        slab_output_params_t *oparams, slab_output_params_t *newoparams, u64 oparams_size, u64 iparams_size){
    u64 safestack_index =  __xmhfhic_safestack_indices[(u32)cpuid];
    if(safestack_index >=0 && safestack_index < 512) {
        __xmhfhic_safestack[(u32)cpuid][safestack_index].src_slabid = src_slabid;
        __xmhfhic_safestack[(u32)cpuid][safestack_index].dst_slabid = dst_slabid;
        __xmhfhic_safestack[(u32)cpuid][safestack_index].hic_calltype = hic_calltype;
        __xmhfhic_safestack[(u32)cpuid][safestack_index].return_address = return_address;
        __xmhfhic_safestack[(u32)cpuid][safestack_index].oparams = oparams;
        __xmhfhic_safestack[(u32)cpuid][safestack_index].newoparams = newoparams;
        __xmhfhic_safestack[(u32)cpuid][safestack_index].oparams_size = oparams_size;
        __xmhfhic_safestack[(u32)cpuid][safestack_index].iparams_size = iparams_size;

        safestack_index++;
        __xmhfhic_safestack_indices[(u32)cpuid] = safestack_index;
    }
}

void __xmhfhic_safepop(u64 cpuid, u64 *src_slabid, u64 *dst_slabid, u64 *hic_calltype, u64 *return_address,
                       slab_output_params_t **oparams, slab_output_params_t **newoparams, u64 *oparams_size, u64 *iparams_size){
    u64 safestack_index =  __xmhfhic_safestack_indices[(u32)cpuid]-1;
    if(safestack_index >=0 && safestack_index < 512){
        *src_slabid = __xmhfhic_safestack[(u32)cpuid][safestack_index].src_slabid;
        *dst_slabid = __xmhfhic_safestack[(u32)cpuid][safestack_index].dst_slabid;
        *hic_calltype = __xmhfhic_safestack[(u32)cpuid][safestack_index].hic_calltype;
        *return_address = __xmhfhic_safestack[(u32)cpuid][safestack_index].return_address;
        *oparams = __xmhfhic_safestack[(u32)cpuid][safestack_index].oparams;
        *newoparams = __xmhfhic_safestack[(u32)cpuid][safestack_index].newoparams;
        *oparams_size = __xmhfhic_safestack[(u32)cpuid][safestack_index].oparams_size;
        *iparams_size = __xmhfhic_safestack[(u32)cpuid][safestack_index].iparams_size;

        __xmhfhic_safestack_indices[(u32)cpuid] = safestack_index;
    }
}





//HIC runtime trampoline
void __xmhfhic_rtm_trampoline(u64 hic_calltype, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid, u64 src_slabid, u64 cpuid, u64 return_address, u64 return_rsp) {
    u8 __paramsbuffer[1024];


    //_XDPRINTF_("%s[%u]: Trampoline got control: RSP=%016llx\n",
    //                __func__, (u32)cpuid, CASM_FUNCCALL(read_rsp,));

    //_XDPRINTF_("%s[%u]: Trampoline got control: hic_calltype=%x, iparams=%x, iparams_size=%u, \
    //           oparams=%x, oparams_size=%u, dst_slabid=%x, src_slabid=%x, cpuid=%x, return_address=%016llx \
    //           return_rsp=%x\n",
    //                __func__, (u32)cpuid,
    //           hic_calltype, iparams, iparams_size, oparams, oparams_size,
    //           dst_slabid, src_slabid, cpuid, return_address, return_rsp);

    switch(hic_calltype){

        case XMHF_HIC_SLABCALL:{
            //check to see if source slab can invoke destination slab
            if(!__xmhfhic_callcaps(src_slabid, dst_slabid)){
                _XDPRINTF_("%s[%u]: Fatal: Slab %u does not have capabilities to invoke Slab %u. Halting!\n",
                    __func__, (u32)cpuid, src_slabid, dst_slabid);
                HALT();
            }


            switch(_xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtype){

                case XMHFGEHIC_SLAB_X86VMXX86PC_HYPERVISOR:{
                    slab_input_params_t *newiparams;
                    slab_output_params_t *newoparams;

                    //save return RSP
                    _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtos[(u32)cpuid] = return_rsp;

                    #if !defined (__XMHF_VERIFICATION__)
                    //copy iparams to internal buffer __paramsbuffer
                    memcpy(&__paramsbuffer, iparams, (iparams_size > 1024 ? 1024 : iparams_size) );
                    #endif

                    //switch to destination slab page tables
 CASM_FUNCCALL(write_cr3,_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3);

                    //make space on destination slab stack for iparams and copy iparams and obtain newiparams
                    {
                        _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid] -= iparams_size;
                        newiparams = (slab_input_params_t *) _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid];
                        #if !defined (__XMHF_VERIFICATION__)
                        memcpy((void *)_xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid],
                               &__paramsbuffer, (iparams_size > 1024 ? 1024 : iparams_size) );
                        #endif
                    }


                    //make space on destination slab stack for oparams and obtain newoparams
                    {
                        _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid] -= oparams_size;
                        newoparams = (slab_output_params_t *) _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid];
                    }


                    //push cpuid, src_slabid, dst_slabid, hic_calltype, return_address, oparams, new oparams and oparams_size tuple to
                    //safe stack
                    //_XDPRINTF_("%s[%u]: safepush: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x, ra=%016llx, \
                    //           op=%016llx, newop=%016llx, opsize=%u\n",
                    //        __func__, (u32)cpuid,
                    //           cpuid, src_slabid, dst_slabid, hic_calltype, return_address,
                    //           oparams, newoparams, oparams_size);

                    __xmhfhic_safepush(cpuid, src_slabid, dst_slabid, hic_calltype, return_address, oparams, newoparams, oparams_size, iparams_size);


                    //jump to destination slab entrystub
 CASM_FUNCCALL(__xmhfhic_trampoline_slabxfer_h2h,newiparams, iparams_size,
                            _xmhfhic_common_slab_info_table[dst_slabid].entrystub,
                            _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid],
                            newoparams, oparams_size,
                            src_slabid, cpuid
                            );

                }
                break;

                case HIC_SLAB_X86VMXX86PC_GUEST:{

                    //_XDPRINTF_("%s[%u]: going to invoke guest slab %u\n",
                    //           __func__, (u32)cpuid, dst_slabid);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VPID, dst_slabid+1);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, _xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RSP, _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RIP, _xmhfhic_common_slab_info_table[dst_slabid].entrystub);

 CASM_FUNCCALL(__xmhfhic_trampoline_slabxfer_h2g,CASM_NOPARAM);


                }
                break;


                default:
                    _XDPRINTF_("%s[%u]: Unknown slabtype=%x. Halting!\n", __func__, (u32)cpuid, hic_calltype);
                    HALT();

            }


        }
        break;

        case XMHF_HIC_SLABRET:{
            __xmhfhic_safestack_element_t elem;

            //pop tuple from safe stack
            __xmhfhic_safepop(cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.return_address,
                                &elem.oparams, &elem.newoparams, &elem.oparams_size, &elem.iparams_size);

            //_XDPRINTF_("%s[%u]: safepop: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x, ra=%016llx, \
            //           op=%016llx, newop=%016llx, opsize=%u\n",
            //        __func__, (u32)cpuid,
            //           cpuid, elem.src_slabid, elem.dst_slabid, elem.hic_calltype, elem.return_address,
            //           elem.oparams, elem.newoparams, elem.oparams_size);

            //check to ensure this SLABRET is paired with a prior SLABCALL
            if ( !((elem.src_slabid == dst_slabid) && (elem.dst_slabid == src_slabid) && (elem.hic_calltype ==XMHF_HIC_SLABCALL)) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRET does not match prior SLABCALL. Halting!\n",
                    __func__, (u32)cpuid);
                HALT();
            }


            #if !defined (__XMHF_VERIFICATION__)
            //copy newoparams to internal buffer __paramsbuffer
            memcpy(&__paramsbuffer, elem.newoparams, (elem.oparams_size > 1024 ? 1024 : elem.oparams_size) );
            #endif

            //adjust slab stack by popping off iparams_size and oparams_size
             _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtos[(u32)cpuid] += (elem.iparams_size+elem.oparams_size);

            //switch to destination slab page tables
 CASM_FUNCCALL(write_cr3,_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3);


            #if !defined (__XMHF_VERIFICATION__)
            //copy internal buffer __paramsbuffer to oparams
            memcpy(elem.oparams, &__paramsbuffer, (elem.oparams_size > 1024 ? 1024 : elem.oparams_size) );
            #endif

            //return back to slab
            //sysexitq(elem.return_address, _xmhfhic_common_slab_info_table[elem.src_slabid].archdata.slabtos[(u32)cpuid]);
            _XDPRINTF_("%s: Halting, sysexit harness not tied in yet!\n", __func__);
            HALT();
        }
        break;














        case XMHF_HIC_SLABCALLEXCEPTION:{
                slab_input_params_t *newiparams;
                slab_output_params_t *newoparams;

                //force destination slab to be the exception slab
                #if defined (__XMHF_VERIFICATION__)
                dst_slabid = 0;
                #else
                dst_slabid = XMHF_HYP_SLAB_XCEXHUB;
                #endif // defined

                //save return RSP
                 _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtos[(u32)cpuid] = return_rsp;

                #if !defined (__XMHF_VERIFICATION__)
                //copy iparams to internal buffer __paramsbuffer
                memcpy(&__paramsbuffer, iparams, (iparams_size > 1024 ? 1024 : iparams_size) );
                #endif

                //switch to destination slab page tables
 CASM_FUNCCALL(write_cr3,_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3);

                //make space on destination slab stack for iparams and copy iparams and obtain newiparams
                {
                     _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid] -= iparams_size;
                    newiparams = (slab_input_params_t *)  _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid];
                    #if !defined (__XMHF_VERIFICATION__)
                    memcpy((void *) _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid],
                           &__paramsbuffer, (iparams_size > 1024 ? 1024 : iparams_size) );
                    #endif
                }

                //push cpuid, src_slabid, dst_slabid, hic_calltype, return_address, iparams, new iparams and iparams_size tuple to
                //safe stack
                //_XDPRINTF_("%s[%u]: safepush: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x, ra=%016llx, \
                //           ip=%016llx, newip=%016llx, ipsize=%u\n",
                //        __func__, (u32)cpuid,
                //           cpuid, src_slabid, dst_slabid, hic_calltype, return_address,
                //           iparams, newiparams, iparams_size);

                __xmhfhic_safepush(cpuid, src_slabid, dst_slabid, hic_calltype, return_address, iparams, newiparams, 0, iparams_size);


                //jump to exception slab entrystub
 CASM_FUNCCALL(__xmhfhic_trampoline_slabxfer_callexception,newiparams, iparams_size,
                                                 _xmhfhic_common_slab_info_table[dst_slabid].entrystub,
                                                 _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid],
                                                 src_slabid, cpuid);


        }
        break;



        case XMHF_HIC_SLABRETEXCEPTION:{
            __xmhfhic_safestack_element_t elem;

            //check to ensure that we get SLABRETEXCEPTION only from the exception slab
            if ( !(src_slabid == XMHF_HYP_SLAB_XCEXHUB) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRETEXCEPTION from a non-exception slab. Halting!\n",
                    __func__, (u32)cpuid);
                HALT();
            }

            //pop tuple from safe stack
            __xmhfhic_safepop(cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.return_address,
                                &elem.oparams, &elem.newoparams, &elem.oparams_size, &elem.iparams_size);

            //_XDPRINTF_("%s[%u]: safepop: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x, ra=%016llx, \
            //           op=%016llx, newop=%016llx, opsize=%u\n",
            //        __func__, (u32)cpuid,
            //           cpuid, elem.src_slabid, elem.dst_slabid, elem.hic_calltype, elem.return_address,
            //           elem.oparams, elem.newoparams, elem.oparams_size);

            //check to ensure this SLABRETEXCEPTION is paired with a prior SLABCALLEXCEPTION
            if ( !((elem.src_slabid == dst_slabid) && (elem.dst_slabid == src_slabid) && (elem.hic_calltype ==XMHF_HIC_SLABCALLEXCEPTION)) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRETEXCEPTION does not match prior SLABCALLEXCEPTION. Halting!\n",
                    __func__, (u32)cpuid);
                HALT();
            }

            //adjust slab stack by popping off iparams_size
             _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtos[(u32)cpuid] += (elem.iparams_size);

            //switch to destination slab page tables
 CASM_FUNCCALL(write_cr3,_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3);

            //return back to slab where exception originally occurred
            {
                    #if !defined (__XMHF_VERIFICATION__)
                    x86vmx_exception_frame_errcode_t *exframe = (x86vmx_exception_frame_errcode_t *)elem.oparams;
                    exframe->orig_rip = elem.return_address;
                    #endif

                    _XDPRINTF_("%s[%u]: returning from exception to %016llx\n",
                        __func__, (u32)cpuid, exframe->orig_rip);


 CASM_FUNCCALL(__xmhfhic_trampoline_slabxfer_retexception,(u64)exframe);

            }

        }
        break;















        case XMHF_HIC_SLABCALLINTERCEPT:{
            //force destination slab to be the intercept slab
            #if defined (__XMHF_VERIFICATION__)
            dst_slabid = 0;
            #else
            dst_slabid = XMHF_HYP_SLAB_XCIHUB;
            #endif // defined

            //_XDPRINTF_("%s[%u]: Trampoline Intercept call\n",
            //        __func__, (u32)cpuid, CASM_FUNCCALL(read_rsp,));

            #if !defined (__XMHF_VERIFICATION__)
            //copy iparams (CPU GPR state) into arch. data for cpuid
            memcpy(&__xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
                   iparams, iparams_size);
            #endif

            //push cpuid, src_slabid, dst_slabid, hic_calltype tuple to
            //safe stack
            //_XDPRINTF_("%s[%u]: safepush: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x\n",
            //        __func__, (u32)cpuid,
            //           cpuid, src_slabid, dst_slabid, hic_calltype);

            __xmhfhic_safepush(cpuid, src_slabid, dst_slabid, hic_calltype, 0, 0, 0, 0, 0);


            //switch to destination slab page tables
            //XXX: eliminate this by preloading VMCS CR3 with xcihub CR3
 CASM_FUNCCALL(write_cr3,_xmhfhic_common_slab_info_table[dst_slabid].archdata.mempgtbl_cr3);

            //intercept slab does not get any input parameters and does not
            //return any output parameters
            //jump to intercept slab entrystub
 CASM_FUNCCALL(__xmhfhic_trampoline_slabxfer_callintercept,_xmhfhic_common_slab_info_table[dst_slabid].entrystub,
                                                         _xmhfhic_common_slab_info_table[dst_slabid].archdata.slabtos[(u32)cpuid],
                                                 src_slabid, cpuid);

        }
        break;



        case XMHF_HIC_SLABRETINTERCEPT:{
            __xmhfhic_safestack_element_t elem;

            //check to ensure that we get SLABRETINTERCEPT only from the intercept slab
            if ( !(src_slabid == XMHF_HYP_SLAB_XCIHUB) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRETINTERCEPT from a non-intercept slab. Halting!\n",
                    __func__, (u32)cpuid);
                HALT();
            }


            //pop tuple from safe stack
            __xmhfhic_safepop(cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.return_address,
                                &elem.oparams, &elem.newoparams, &elem.oparams_size, &elem.iparams_size);

            //_XDPRINTF_("%s[%u]: safepop: {cpuid: %016llx, srcsid: %u, dstsid: %u, ctype: %x\n",
            //        __func__, (u32)cpuid,
            //           cpuid, elem.src_slabid, elem.dst_slabid, elem.hic_calltype);

            //check to ensure this SLABRETINTERCEPT is paired with a prior SLABCALLINTERCEPT
            if ( !((elem.src_slabid == dst_slabid) && (elem.dst_slabid == src_slabid) && (elem.hic_calltype ==XMHF_HIC_SLABCALLINTERCEPT)) ){
                _XDPRINTF_("%s[%u]: Fatal: SLABRETINTERCEPT does not match prior SLABCALLINTERCEPT. Halting!\n",
                    __func__, (u32)cpuid);
                HALT();
            }

            //resume caller (guest) slab where the intercept was triggered
 CASM_FUNCCALL(__xmhfhic_trampoline_slabxfer_retintercept,(u64)&__xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs);

        }
        break;














        default:
            _XDPRINTF_("%s[%u]: Unknown hic_calltype=%x. Halting!\n",
                    __func__, (u32)cpuid, hic_calltype);
            HALT();


    }

    _XDPRINTF_("%s[%u]: Should never come here. Halting!\n",
                    __func__, (u32)cpuid);
    HALT();
}

#endif //0





//////
// sentinel stubs, invoked by their CASM counterparts
//////

/*static void _geec_sentinel_dump_exframe(x86vmx_exception_frame_t *exframe){
    //dump relevant info
    _XDPRINTF_("%s: [START]\n\n", __func__);
    _XDPRINTF_("exception %x\n", exframe->vector);
    _XDPRINTF_("errorcode=0x%08x\n", exframe->error_code);
    _XDPRINTF_("CS:EIP:EFLAGS = 0x%08x:0x%08x:0x%08x\n", exframe->orig_cs, exframe->orig_rip, exframe->orig_rflags);
    _XDPRINTF_("SS:ESP = 0x%08x:0x%08x\n", exframe->orig_ss, exframe->orig_rsp);
    _XDPRINTF_("EAX=0x%08x, EBX=0x%08x\n", exframe->eax, exframe->ebx);
    _XDPRINTF_("ECX=0x%08x, EDX=0x%08x\n", exframe->ecx, exframe->edx);
    _XDPRINTF_("ESI=0x%08x, EDI=0x%08x\n", exframe->esi, exframe->edi);
    _XDPRINTF_("EBP=0x%08x, ESP=0x%08x\n", exframe->ebp, exframe->esp);
    _XDPRINTF_("%s: [END]\n\n", __func__);
}*/

////// exceptions

void _geec_sentinel_exception_stub(x86vmx_exception_frame_t *exframe){
    slab_params_t spl;

    memset(&spl, 0, sizeof(spl));


    spl.slab_ctype = XMHFGEEC_SENTINEL_CALL_EXCEPTION;
    spl.src_slabid = XMHF_HYP_SLAB_GEECSENTINEL; //XXX: TODO: grab src_slabid based on exframe->orig_rip
    spl.dst_slabid = XMHF_HYP_SLAB_XCEXHUB;
    spl.cpuid = __xmhfhic_x86vmx_cpuidtable[xmhf_baseplatform_arch_x86_getcpulapicid()];
    memcpy(&spl.in_out_params[0], exframe,
           sizeof(x86vmx_exception_frame_t));

    //_geec_sentinel_dump_exframe(spl.in_out_params);
    geec_sentinel_main(&spl, &spl);
}


void __xmhfhic_rtm_intercept(x86regs_t *r){
    slab_params_t spl;
    //xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
    //    (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;

    memset(&spl, 0, sizeof(spl));

    spl.src_slabid = CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VPID);
    spl.cpuid = __xmhfhic_x86vmx_cpuidtable[xmhf_baseplatform_arch_x86_getcpulapicid()];

    //copy incoming register state
    memcpy(&spl.in_out_params[0], r, sizeof(x86regs_t));

    //call xcihub
    spl.dst_slabid = XMHF_HYP_SLAB_XCIHUB;
    XMHF_SLAB_CALLNEW(&spl);

    //store updated register state
    memcpy(r, &spl.in_out_params[0], sizeof(x86regs_t));




    /*
    //TODO: x86_64--> x86
	asm volatile(
                        "pushq %%rsp \r\n"
                        "pushq %%rbp \r\n"
                        "pushq %%rdi \r\n"
                        "pushq %%rsi \r\n"
                        "pushq %%rdx \r\n"
                        "pushq %%rcx \r\n"
                        "pushq %%rbx \r\n"
                        "pushq %%rax \r\n"
                        "pushq %%r15 \r\n"
                        "pushq %%r14 \r\n"
                        "pushq %%r13 \r\n"
                        "pushq %%r12 \r\n"
                        "pushq %%r11 \r\n"
                        "pushq %%r10 \r\n"
                        "pushq %%r9 \r\n"
                        "pushq %%r8 \r\n"

                        "pushfq \r\n"
                        "popq %%rax \r\n"
                        "orq $0x3000, %%rax \r\n"
                        "pushq %%rax \r\n"
                        "popfq \r\n"

                        //rdi = hic_calltype = XMHF_HIC_SLABCALLINTERCEPT
                        "movq %0, %%rdi \r\n"

                        //iparams
                        "movq %%rsp, %%rsi \r\n"

                        //iparams_size
                        "movq %1, %%rdx \r\n"

                        //oparams
                        "movq %%rsi, %%rcx \r\n"

                        //oparams_size
                        "movq %%rdx, %%r8 \r\n"

                        //dst_slabid
                        "movq %2, %%r9 \r\n"

                        //return_rsp (NA -- since its stored in VMCS)
                        "pushq $0x0 \r\n"

                        //return_address (NA -- since its stored in VMCS)
                        "pushq $0x0 \r\n"

                        //cpuid
                        "movq %3, %%rax \r\n"       //RAX=X86XMP_LAPIC_ID_MEMORYADDRESS
                        "movl (%%eax), %%eax\r\n"   //EAX(bits 0-7)=LAPIC ID
                        "shrl $24, %%eax\r\n"       //EAX=LAPIC ID
                        "movq __xmhfhic_x86vmx_cpuidtable+0x0(,%%eax,8), %%rax\r\n" //RAX = 0-based cpu index for the CPU
                        "pushq %%rax \r\n"

                        //src_slabid
                        "movq %4, %%rax \r\n"
                        "vmread %%rax, %%rax \r\n"     //RAX = VPID = slab_id
                        "decq %%rax \r\n"
                        "pushq %%rax \r\n"


                        "callq __xmhfhic_rtm_trampoline \r\n"
					:
					:   "i" (XMHF_HIC_SLABCALLINTERCEPT),
                        "i" (sizeof(x86regs64_t)),
                        "i" (XMHF_HYP_SLAB_XCIHUB),
					    "i" (X86SMP_LAPIC_ID_MEMORYADDRESS),
                        "i" (VMCS_CONTROL_VPID)
                    :
		);

*/

}






/////

void geec_sentinel_main(slab_params_t *sp, void *caller_stack_frame){

    switch(sp->slab_ctype){
        case XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_VfT_uVU_uVT_PROG_uVU_uVT_PROG_GUEST:{

            switch (_xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.slabtype){

                case XMHFGEEC_SLABTYPE_VfT_PROG:{
                    CASM_FUNCCALL(_geec_sentinel_xfer_vft_prog_to_vft_prog,
                                  _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub,
                                  caller_stack_frame);
                    _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                               __LINE__);
                    HALT();

                }
                break;

                case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
                case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
                case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
                    u32 errorcode;
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VPID, sp->dst_slabid );
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, (_xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.mempgtbl_cr3  | 0x1E) );
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_HIGH, 0);
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RSP, _xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.slabtos[(u16)sp->cpuid]);
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RIP, _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub);

                    errorcode = CASM_FUNCCALL(_geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog_guest, CASM_NOPARAM);

                    switch(errorcode){
                        case 0:	//no error code, VMCS pointer is invalid
                            _XDPRINTF_("GEEC_SENTINEL: VMLAUNCH error; VMCS pointer invalid?\n");
                            break;
                        case 1:{//error code available, so dump it
                            u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
                            _XDPRINTF_("GEEC_SENTINEL: VMLAUNCH error; code=%x\n", code);
                            break;
                        }
                    }

                    HALT();

                }
                break;

                default:
                    _XDPRINTF_("GEEC_SENTINEL(ln:%u): Unrecognized transition. Halting!", __LINE__);
                    HALT();
            }


        }
        break;





        case XMHFGEEC_SENTINEL_CALL_EXCEPTION:{
            if(!(_xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.slabtype == XMHFGEEC_SLABTYPE_VfT_PROG_EXCEPTION)){
                _XDPRINTF_("GEEC_SENTINEL(ln:%u): exception target slab not VfT_PROG. Halting!\n");
                HALT();
            }

            CASM_FUNCCALL(_geec_sentinel_xfer_exception_to_vft_prog,
              _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub,
              caller_stack_frame);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                       __LINE__);
            HALT();

        }
        break;






        case XMHFGEEC_SENTINEL_RET_EXCEPTION:{
            if(!
               (_xmhfhic_common_slab_info_table[sp->src_slabid].archdata.slabtype == XMHFGEEC_SLABTYPE_VfT_PROG_EXCEPTION &&
                sp->dst_slabid == XMHF_HYP_SLAB_GEECSENTINEL)){
                _XDPRINTF_("GEEC_SENTINEL(ln:%u): exception ret source slab not VfT_PROG_EXCEPTION. Halting!\n");
                HALT();
            }

            //_geec_sentinel_dump_exframe(sp->in_out_params);

            CASM_FUNCCALL(_geec_sentinel_xfer_ret_from_exception,
                sp->in_out_params);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                       __LINE__);
            HALT();

        }
        break;







        default:
            _XDPRINTF_("GEEC_SENTINEL: unkown call type %x. Halting!\n", sp->slab_ctype);
            HALT();

    }

}


