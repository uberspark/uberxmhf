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
 * HIC UAPI (micro-API) implementation for XMHF
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-hic.h>
#include <xmhf-debug.h>

//extern x_slab_info_t _xmhfhic_common_slab_info_table[XMHF_HIC_MAX_SLABS];
extern u64 guestslab_mempgtbl_buffer[1048576];


/////
// forward prototypes

//static void __xmhfhic_rtm_uapihandler_cpustate(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid);
//static void __xmhfhic_rtm_uapihandler_physmem(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid);
//static void __xmhfhic_rtm_uapihandler_mempgtbl(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid);

static void __xmhfhic_rtm_uapihandler_cpustate(slab_params_t *sp);
static void __xmhfhic_rtm_uapihandler_physmem(slab_params_t *sp);
static void __xmhfhic_rtm_uapihandler_mempgtbl(slab_params_t *sp);



static bool _uapicheck_is_within_slab_memory_extents(u64 slab_id, u64 addr, u64 size){
    u64 i;
    bool status=false;

    for(i=0; i < HIC_SLAB_PHYSMEM_MAXEXTENTS; i++){
        if(_xmhfhic_common_slab_info_table[slab_id].slab_physmem_extents[i].addr_start == 0 &&
           _xmhfhic_common_slab_info_table[slab_id].slab_physmem_extents[i].addr_end == 0)
           continue;

        if(addr >= _xmhfhic_common_slab_info_table[slab_id].slab_physmem_extents[i].addr_start &&
           (addr+size) < _xmhfhic_common_slab_info_table[slab_id].slab_physmem_extents[i].addr_end)
            return true;

    }

    return status;
}

static bool _uapicheck_encoding_used_by_hic(u64 encoding){
    if( (u32)encoding & 0xFFFF0000 )
        return false;

    if( (u16)encoding == 0x0000 || (u16)encoding == 0x4000 || (u16)encoding == 0x4002 || (u16)encoding == 0x401E )
        return true;

    if( ((u16)encoding & 0xFF00) == 0x20 ||
       ((u16)encoding & 0xFF00) == 0x6C ||
       ((u16)encoding & 0xFF00) == 0x4C ||
       ((u16)encoding & 0xFF00) == 0x2C ||
       ((u16)encoding & 0xFF00) == 0x0C)
        return true;

    return false;
}


//uapicall = sp->slab_ctype
//uapicall_num = sp->in_out_params[0];
//uapicall_subnum  = sp->in_out_params[1];
//cpuid = sp->cpuid


//////
// main UAPI handler, gets called by a slab
// src_slabid and cpuid are trusted input parameters provided by HIC
//void __xmhfhic_rtm_uapihandler(u64 uapicall, u64 uapicall_num, u64 uapicall_subnum,
//                               u64 reserved, u64 iparams, u64 oparams,
//                               u64 src_slabid, u64 cpuid){
void __xmhfhic_rtm_uapihandler(slab_params_t *sp){


    //_XDPRINTF_("%s[%u]: uapi handler got control: uapicall=%x, uapicall_num=%x, \
    //           uapicall_subnum=%x, iparams=%x, oparams=%x, \
    //           src_slabid=%u, cpuid=%x, cr3=%x\n",
    //            __func__, (u32)cpuid,
    //           uapicall, uapicall_num, uapicall_subnum,
    //           iparams, oparams,
    //           src_slabid, cpuid, CASM_FUNCCALL(read_cr3,));

    //checks
    //1. src_slabid is a hypervisor slab
    if( !(_xmhfhic_common_slab_info_table[sp->src_slabid].archdata.slabtype == HIC_SLAB_X86VMXX86PC_HYPERVISOR) ){
        _XDPRINTF_("%s[%u]: uapierr: src_slabid (%u) is not a hypervisor slab. Halting!\n", __func__, (u16)sp->cpuid, sp->src_slabid);
        //HALT();
        return;
    }

    #if defined (__XMHF_VERIFICATION__)
    assert( _xmhfhic_common_slab_info_table[src_slabid].archdata.slabtype == HIC_SLAB_X86VMXX86PC_HYPERVISOR );
    #endif //__XMHF_VERIFICATION__


    //2. src_slabid should have capabilities for the requested uapicall_num
    if( !(_xmhfhic_common_slab_info_table[sp->src_slabid].slab_uapicaps & HIC_SLAB_UAPICAP(sp->in_out_params[0])) ){
        _XDPRINTF_("%s[%u]: uapierr: src_slabid (%u) does not have uapi capability. Halting!\n", __func__, (u16)sp->cpuid, sp->src_slabid);
        //HALT();
        return;
    }


    #if defined (__XMHF_VERIFICATION__)
        assert( _xmhfhic_common_slab_info_table[src_slabid].slab_uapicaps & HIC_SLAB_UAPICAP(uapicall_num));
    #endif //__XMHF_VERIFICATION__



    switch(sp->in_out_params[0]){
        case XMHF_HIC_UAPI_CPUSTATE:
            //__xmhfhic_rtm_uapihandler_cpustate(uapicall_subnum, iparams, oparams, cpuid, src_slabid);
            __xmhfhic_rtm_uapihandler_cpustate(sp);
            break;

        case XMHF_HIC_UAPI_PHYSMEM:
            //__xmhfhic_rtm_uapihandler_physmem(uapicall_subnum, iparams, oparams, cpuid, src_slabid);
            __xmhfhic_rtm_uapihandler_physmem(sp);
            break;

        case XMHF_HIC_UAPI_MEMPGTBL:
            //__xmhfhic_rtm_uapihandler_mempgtbl(uapicall_subnum, iparams, oparams, cpuid, src_slabid);
            __xmhfhic_rtm_uapihandler_mempgtbl(sp);
            break;


        default:
            _XDPRINTF_("%s[%u]: Unknown UAPI call %x. Halting!\n",
                    __func__, (u16)sp->cpuid, sp->in_out_params[0]);
            //HALT();
            return;
    }


    return;
}










//////
// cpustate UAPI sub-handler
//static void __xmhfhic_rtm_uapihandler_cpustate(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid){
static void __xmhfhic_rtm_uapihandler_cpustate(slab_params_t *sp){
    //_XDPRINTF_("%s[%u]: Got control...\n", __func__, (u32)cpuid);

    switch(sp->in_out_params[1]){
        case XMHF_HIC_UAPI_CPUSTATE_VMREAD:{
            //input: encoding (u64) = in_out_params[2], [3]
            //output: u64 = in_out_params[4], [5]

            //checks:
            /*//1. oparams should be within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(u64))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined(__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(u64)));
            #endif // defined

            /*//2. encoding cannot contain any value that is specific to HIC
            if(_uapicheck_encoding_used_by_hic(iparams)){
                _XDPRINTF_("%s[%u],%u: uapierr: encoding reserved for HIC. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined(__XMHF_VERIFICATION__)
            assert(!_uapicheck_encoding_used_by_hic(iparams));
            #endif // defined

            #if !defined(__XMHF_VERIFICATION__)
            {
                u64 encoding = ((u64)sp->in_out_params[3] << 32) | (u64)sp->in_out_params[2];
                u64 value = CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,encoding);
                sp->in_out_params[5] = (value >> 32);
                sp->in_out_params[4] = (u32)value;
            }
            // *(u64 *)oparams = CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,iparams);
            #endif // defined

        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_VMWRITE:{
            //input: encoding (u64) = in_out_params[2], [3]
            //input: value (u64) = in_out_params[4], [5]

            //checks:
            /*//1. encoding cannot contain any value that is specific to HIC
            if(_uapicheck_encoding_used_by_hic(iparams)){
                _XDPRINTF_("%s[%u],%u: uapierr: encoding reserved for HIC. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined(__XMHF_VERIFICATION__)
            assert(!_uapicheck_encoding_used_by_hic(iparams));
            #endif // defined

            #if !defined(__XMHF_VERIFICATION__)
            {
              u64 encoding = ((u64)sp->in_out_params[3] << 32) | sp->in_out_params[2];
              u64 value = ((u64)sp->in_out_params[5] << 32) | sp->in_out_params[4];
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,encoding, value);
            }
            #endif
        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD:{
            //output = in_out_params[2..9] = x86regs_t

            /*//checks:
            //1. oparams should be within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(x86regs64_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined(__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(x86regs64_t)));
            #endif // defined

            #if !defined (__XMHF_VERIFICATION__)
            //memcpy(oparams, & __xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
            //       sizeof(x86regs64_t));
            memcpy(&sp->in_out_params[2],
                   &__xmhfhic_x86vmx_archdata[(u16)sp->cpuid].vmx_gprs,
                   sizeof(x86regs_t));

            #endif
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE:{
            //input: in_out_params[2..9] = x86regs_t

            //checks:
            /*//1. iparams should be within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(x86regs64_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined(__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(x86regs64_t)));
            #endif // defined

            #if !defined (__XMHF_VERIFICATION__)
            memcpy(&__xmhfhic_x86vmx_archdata[(u16)sp->cpuid].vmx_gprs,
                   &sp->in_out_params[2],
                   sizeof(x86regs_t));
            #endif
        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_WRMSR:{
            //input: msr (u32) = in_out_params[2]
            //input: value (u64) = in_out_params[3], [4]

            //checks
            /*//1. msr cannot contain any value that is specific to HIC
            if(!( iparams != MSR_EFER && iparams != IA32_SYSENTER_CS_MSR && iparams != IA32_SYSENTER_EIP_MSR && iparams != IA32_SYSENTER_ESP_MSR)){
                _XDPRINTF_("%s[%u],%u: uapierr: HIC specific iparams being written to. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined(__XMHF_VERIFICATION__)
            assert(( iparams != MSR_EFER && iparams != IA32_SYSENTER_CS_MSR && iparams != IA32_SYSENTER_EIP_MSR && iparams != IA32_SYSENTER_ESP_MSR));
            #endif // defined


            #if !defined (__XMHF_VERIFICATION__)
            {
                u32 msr = sp->in_out_params[2];
                u64 value = ((u64)sp->in_out_params[4] << 32) | sp->in_out_params[3];
 CASM_FUNCCALL(wrmsr64,msr, value);
            }
            #endif
        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_RDMSR:{
            //iparams = msr, oparams = (u64 *)
            //input: msr (u32) = in_out_params[2];
            //output: value (u64) = in_out_paams[3], [4];

            //checks:
            /*//1. msr cannot contain any value that is specific to HIC
            if(!( iparams != MSR_EFER && iparams != IA32_SYSENTER_CS_MSR && iparams != IA32_SYSENTER_EIP_MSR && iparams != IA32_SYSENTER_ESP_MSR)){
                _XDPRINTF_("%s[%u],%u: uapierr: HIC specific MSR being read from. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined(__XMHF_VERIFICATION__)
            assert(( iparams != MSR_EFER && iparams != IA32_SYSENTER_CS_MSR && iparams != IA32_SYSENTER_EIP_MSR && iparams != IA32_SYSENTER_ESP_MSR));
            #endif // defined

            /*//2. oparams should be within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(u64))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined(__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(u64)));
            #endif // defined


            #if !defined (__XMHF_VERIFICATION__)
            {
                u32 msr = sp->in_out_params[2];
                u64 value = CASM_FUNCCALL(rdmsr64,msr);
                sp->in_out_params[4] = value >> 32;
                sp->in_out_params[3] = (u32)value;
            }
            // *(u64 *)oparams = CASM_FUNCCALL(rdmsr64,(u32)iparams);
            #endif
        }
        break;

        default:
            _XDPRINTF_("%s[%u]: Unknown cpustate subcall %x. Halting!\n",
                    __func__, (u16)sp->cpuid, sp->in_out_params[1]);
            //HALT();
            return;
    }

}










//////
// physmem UAPI sub-handler
//static void __xmhfhic_rtm_uapihandler_physmem(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid){
static void __xmhfhic_rtm_uapihandler_physmem(slab_params_t *sp){
    //_XDPRINTF_("%s[%u]: Got control...\n", __func__, (u32)cpuid);

    switch(sp->in_out_params[1]){
        case XMHF_HIC_UAPI_PHYSMEM_PEEK:{
            //input: in_out_params[2..5] = xmhf_hic_uapi_physmem_desc_t
            xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&sp->in_out_params[2];


            //checks:
            /*//1. iparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_physmem_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: iparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/



            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_physmem_desc_t)));
            #endif // defined

            //2. destination slab is within bounds and is a guest slab
            if(! (pdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is out of bounds. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((pdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ));
            #endif // defined

            if( !(_xmhfhic_common_slab_info_table[pdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is not a guest slab. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((_xmhfhic_common_slab_info_table[pdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST));
            #endif // defined


            //3. pdesc->addr_from and pdesc->numbytes is within destination slab memory extents
            /*if(!_uapicheck_is_within_slab_memory_extents(pdesc->guest_slab_index, pdesc->addr_from, pdesc->numbytes)){
                _XDPRINTF_("%s[%u],%u: uapierr: addr_from is not within destination slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(pdesc->guest_slab_index, pdesc->addr_from, pdesc->numbytes));
            #endif // defined


            //4. pdesc->addr_to is within source slab memory extents
            /*if(!_uapicheck_is_within_slab_memory_extents(src_slabid, pdesc->addr_to, pdesc->numbytes)){
                _XDPRINTF_("%s[%u],%u: uapierr: addr_to is not within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, pdesc->addr_to, pdesc->numbytes));
            #endif // defined

            #if !defined (__XMHF_VERIFICATION__)
            memcpy(pdesc->addr_to, pdesc->addr_from, pdesc->numbytes);
            #endif
        }
        break;

        case XMHF_HIC_UAPI_PHYSMEM_POKE:{
            //input: in_out_params[2..5] = xmhf_hic_uapi_physmem_desc_t
            xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&sp->in_out_params[2];

            //checks:
            /*//1. iparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_physmem_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: iparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_physmem_desc_t)));
            #endif // defined


            //2. destination slab is within bounds and is a guest slab
            if(! (pdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is out of bounds. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((pdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ));
            #endif // defined


            if( !(_xmhfhic_common_slab_info_table[pdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is not a guest slab. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((_xmhfhic_common_slab_info_table[pdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST));
            #endif // defined

            /*//3. pdesc->addr_to and pdesc->numbytes is within destination slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(pdesc->guest_slab_index, pdesc->addr_to, pdesc->numbytes)){
                _XDPRINTF_("%s[%u],%u: uapierr: addr_to is not within destination slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(pdesc->guest_slab_index, pdesc->addr_to, pdesc->numbytes));
            #endif // defined


            //4. pdesc->addr_from is within source slab memory extents
            /*if(!_uapicheck_is_within_slab_memory_extents(src_slabid, pdesc->addr_from, pdesc->numbytes)){
                _XDPRINTF_("%s[%u],%u: uapierr: addr_to is not within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, pdesc->addr_from, pdesc->numbytes));
            #endif // defined

            #if !defined (__XMHF_VERIFICATION__)
            memcpy(pdesc->addr_to, pdesc->addr_from, pdesc->numbytes);
            #endif
        }
        break;


        default:
            _XDPRINTF_("%s[%u]: Unknown physmem subcall %x. Halting!\n",
                    __func__, (u16)sp->cpuid, sp->in_out_params[1]);
            //HALT();
            return;

    }

}









//////
// mempgtbl UAPI sub-handler
static void __xmhfhic_rtm_uapihandler_mempgtbl(slab_params_t *sp){
    _XDPRINTF_("%s[%u]: Got control...\n", __func__, (u16)sp->cpuid);

    switch(sp->in_out_params[1]){
        case XMHF_HIC_UAPI_MEMPGTBL_GETENTRY:{
            //input/output = in_out_params[2..7]
            xmhf_hic_uapi_mempgtbl_desc_t *mdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)&sp->in_out_params[2];

            //checks:
            /*//1. iparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: iparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t)) );
            #endif // defined

            //2. oparams is within source slab memory extents
            /*if(!_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t)) );
            #endif // defined

            //3. destination slab is within bounds and is a guest slab
            if(! (mdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is out of bounds. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((imdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ));
            #endif // defined


            if( !(_xmhfhic_common_slab_info_table[mdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is not a guest slab. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((_xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST));
            #endif // defined

            //u64 pdpt_index = pae_get_pdpt_index(imdesc->gpa);
            //u64 pd_index = pae_get_pdt_index(imdesc->gpa);
            //u64 pt_index = pae_get_pt_index(imdesc->gpa);
            u32 pt_index = mdesc->gpa/PAGE_SIZE_4K;

            //checks:
            //4. iparams->gpa fits within destination slab mempgtbl extents (pdpt_index, pd_index and pt_index bounds)
            if( !(pt_index < 1048576) ){
                _XDPRINTF_("%s[%u],%u: uapierr: mempgtbl indices out of bound. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((pt_index < 1048576));
            #endif // defined

            {
                //u64 *table = (u64 *)_xmhfhic_common_slab_info_table[mdesc->guest_slab_index].archdata.mempgtbl_pt;
                //mdesc->entry = table[pt_index];
                u64 pdpt_index = pae_get_pdpt_index(mdesc->gpa);
                u64 pd_index = pae_get_pdt_index(mdesc->gpa);
                u64 pt_index = pae_get_pt_index(mdesc->gpa);
                mdesc->entry = _dbuf_mempgtbl_pt[mdesc->guest_slab_index][pdpt_index][pd_index][pt_index];
            }

            //debug
            //_XDPRINTF_("MEMPGTBL_GETENTRY: guest slab id=%u, gpa=%016llx(index=%u), entry=%016llx\n", mdesc->guest_slab_index,
            //           mdesc->gpa, pt_index, mdesc->entry);

        }
        break;


        case XMHF_HIC_UAPI_MEMPGTBL_SETENTRY:{
            //input = in_out_params[2..7]
            xmhf_hic_uapi_mempgtbl_desc_t *mdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)&sp->in_out_params[2];

            //checks:
            /*//1. iparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: iparams should be within source slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert( _uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t)) );
            #endif // defined


            //2. destination slab is within bounds and is a guest slab
            /*if(! (imdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is out of bounds. Halting!\n", __func__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }*/

            #if defined (__XMHF_VERIFICATION__)
            assert( imdesc->guest_slab_index < XMHF_HIC_MAX_SLABS );
            #endif // defined


            if( !(_xmhfhic_common_slab_info_table[mdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is not a guest slab. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert( _xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST );
            #endif // defined

            //u64 pdpt_index = pae_get_pdpt_index(imdesc->gpa);
            //u64 pd_index = pae_get_pdt_index(imdesc->gpa);
            //u64 pt_index = pae_get_pt_index(imdesc->gpa);
            u32 pt_index = mdesc->gpa/PAGE_SIZE_4K;

            //checks:
            //3. iparams->gpa fits within destination slab mempgtbl extents (pdpt_index, pd_index and pt_index bounds)
            if( !(pt_index < 1048576) ){
                _XDPRINTF_("%s[%u],%u: uapierr: mempgtbl indices out of bound. Halting!\n", __func__, (u16)sp->cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert( (pt_index < 1048576) );
            #endif // defined

            //4. if iparams->entry has present bit set then entry is within destination slab memory extents
            if( mdesc->entry & 0x7 ){
                /*if(!_uapicheck_is_within_slab_memory_extents(imdesc->guest_slab_index, (imdesc->entry & 0xFFFFFFFFFFFFF000UL), 1)){
                    _XDPRINTF_("%s[%u],%u: uapierr: mempgtbl entry is not within destination slab memory extents. Halting!\n", __func__, (u32)cpuid, __LINE__);
                    //HALT();
                    return;
                }*/
                #if defined (__XMHF_VERIFICATION__)
                assert( _uapicheck_is_within_slab_memory_extents(imdesc->guest_slab_index, (imdesc->entry & 0xFFFFFFFFFFFFF000UL), 1) );
                #endif // defined
            }

            {
                //u64 *table = (u64 *)_xmhfhic_common_slab_info_table[mdesc->guest_slab_index].archdata.mempgtbl_pt;
                //table[pt_index] = mdesc->entry;
                u64 pdpt_index = pae_get_pdpt_index(mdesc->gpa);
                u64 pd_index = pae_get_pdt_index(mdesc->gpa);
                u64 pt_index = pae_get_pt_index(mdesc->gpa);
                _dbuf_mempgtbl_pt[mdesc->guest_slab_index][pdpt_index][pd_index][pt_index] = mdesc->entry;

            }

            //#if defined (__XMHF_VERIFICATION__)
            //assert(0);
            //#endif //__XMHF_VERIFICATION__

        }
        break;


        default:
            _XDPRINTF_("%s[%u]: Unknown cpustate subcall %x. Halting!\n",
                    __func__, (u16)sp->cpuid, sp->in_out_params[1]);
            return;

    }

}



