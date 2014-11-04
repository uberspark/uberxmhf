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
 * HIC UAPI (micro-API) verification stub for XMHF
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>


//extern x_slab_info_t _x_xmhfhic_common_slab_info_table[XMHF_HIC_MAX_SLABS];
//extern u64 guestslab_mempgtbl_buffer[1048576];


/////
// forward prototypes

static void __xmhfhic_rtm_uapihandler_cpustate(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid);
static void __xmhfhic_rtm_uapihandler_physmem(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid);
static void __xmhfhic_rtm_uapihandler_mempgtbl(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid);


/*static bool _uapicheck_is_within_slab_memory_extents(u64 slab_id, u64 addr, u64 size){
    u64 i;
    bool status=false;

    for(i=0; i < HIC_SLAB_PHYSMEM_MAXEXTENTS; i++){
        if(_x_xmhfhic_common_slab_info_table[slab_id].slab_physmem_extents[i].addr_start == 0 &&
           _x_xmhfhic_common_slab_info_table[slab_id].slab_physmem_extents[i].addr_end == 0)
           continue;

        if(addr >= _x_xmhfhic_common_slab_info_table[slab_id].slab_physmem_extents[i].addr_start &&
           (addr+size) < _x_xmhfhic_common_slab_info_table[slab_id].slab_physmem_extents[i].addr_end)
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
*/



//////
// main UAPI handler, gets called by a slab
// src_slabid and cpuid are trusted input parameters provided by HIC
void __xmhfhic_rtm_uapihandler(u64 uapicall, u64 uapicall_num, u64 uapicall_subnum,
                               u64 reserved, u64 iparams, u64 oparams,
                               u64 src_slabid, u64 cpuid){

    //_XDPRINTF_("%s[%u]: uapi handler got control: uapicall=%x, uapicall_num=%x, \
    //           uapicall_subnum=%x, iparams=%x, oparams=%x, \
    //           src_slabid=%u, cpuid=%x, cr3=%x\n",
    //            __FUNCTION__, (u32)cpuid,
    //           uapicall, uapicall_num, uapicall_subnum,
    //           iparams, oparams,
    //           src_slabid, cpuid, read_cr3());


/*    //checks
    //1. src_slabid is a hypervisor slab
    if( !(_x_xmhfhic_common_slab_info_table[src_slabid].archdata.slabtype == HIC_SLAB_X86VMXX86PC_HYPERVISOR) ){
        _XDPRINTF_("%s[%u]: uapierr: src_slabid (%u) is not a hypervisor slab. Halting!\n", __FUNCTION__, (u32)cpuid, src_slabid);
        //HALT();
        return;
    }

    #if defined (__XMHF_VERIFICATION__)
    assert( _x_xmhfhic_common_slab_info_table[src_slabid].archdata.slabtype == HIC_SLAB_X86VMXX86PC_HYPERVISOR );
    #endif //__XMHF_VERIFICATION__



    //2. src_slabid should have capabilities for the requested uapicall_num
    if( !(_x_xmhfhic_common_slab_info_table[src_slabid].slab_uapicaps & HIC_SLAB_UAPICAP(uapicall_num)) ){
        _XDPRINTF_("%s[%u]: uapierr: src_slabid (%u) does not have uapi capability. Halting!\n", __FUNCTION__, (u32)cpuid, src_slabid);
        //HALT();
        return;
    }


    #if defined (__XMHF_VERIFICATION__)
        assert( _x_xmhfhic_common_slab_info_table[src_slabid].slab_uapicaps & HIC_SLAB_UAPICAP(uapicall_num));
    #endif //__XMHF_VERIFICATION__
*/


    switch(uapicall_num){
        case XMHF_HIC_UAPI_CPUSTATE:
            __xmhfhic_rtm_uapihandler_cpustate(uapicall_subnum, iparams, oparams, cpuid, src_slabid);
            break;

        case XMHF_HIC_UAPI_PHYSMEM:
             __xmhfhic_rtm_uapihandler_physmem(uapicall_subnum, iparams, oparams, cpuid, src_slabid);
            break;

        case XMHF_HIC_UAPI_MEMPGTBL:
            __xmhfhic_rtm_uapihandler_mempgtbl(uapicall_subnum, iparams, oparams, cpuid, src_slabid);
            break;

        default:
            _XDPRINTF_("%s[%u]: Unknown UAPI call %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_num);
            //HALT();
            return;
    }


    return;
}










//////
// cpustate UAPI sub-handler
static void __xmhfhic_rtm_uapihandler_cpustate(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid){
    //_XDPRINTF_("%s[%u]: Got control...\n", __FUNCTION__, (u32)cpuid);

    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_CPUSTATE_VMREAD:{
            //iparams = encoding (u64), oparams = memory (u64 *)
/*            //checks:
            //1. oparams should be within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(u64))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined(__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(u64)));
            #endif // defined

            //2. encoding cannot contain any value that is specific to HIC
            if(_uapicheck_encoding_used_by_hic(iparams)){
                _XDPRINTF_("%s[%u],%u: uapierr: encoding reserved for HIC. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined(__XMHF_VERIFICATION__)
            assert(!_uapicheck_encoding_used_by_hic(iparams));
            #endif // defined
*/
            {
                u64 value;
                value = nondet_u64();
                *(u64 *)oparams = value;
            }

/*            #if !defined(__XMHF_VERIFICATION__)
            *(u64 *)oparams = xmhfhw_cpu_x86vmx_vmread(iparams);
            #endif // defined
*/

        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_VMWRITE:{
            //iparams = encoding (u64), oparams = value (u64)
/*            //checks:
            //1. encoding cannot contain any value that is specific to HIC
            if(_uapicheck_encoding_used_by_hic(iparams)){
                _XDPRINTF_("%s[%u],%u: uapierr: encoding reserved for HIC. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined(__XMHF_VERIFICATION__)
            assert(!_uapicheck_encoding_used_by_hic(iparams));
            #endif // defined
*/

            //void

/*
            #if !defined(__XMHF_VERIFICATION__)
            xmhfhw_cpu_x86vmx_vmwrite(iparams, oparams);
            #endif
*/


        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD:{
            //iparams = NULL, oparams = x86regs64_t *
/*            //checks:
            //1. oparams should be within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(x86regs64_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined(__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(x86regs64_t)));
            #endif // defined
*/

            {
                x86regs64_t *regs = (x86regs64_t *)oparams;
                regs->rax = nondet_u64();
                regs->rbx = nondet_u64();
                regs->rcx = nondet_u64();
                regs->rdx = nondet_u64();
                regs->rsp = nondet_u64();
                regs->rbp = nondet_u64();
                regs->rsi = nondet_u64();
                regs->rdi = nondet_u64();
                regs->r8 = nondet_u64();
                regs->r9 = nondet_u64();
                regs->r10 = nondet_u64();
                regs->r11 = nondet_u64();
                regs->r12 = nondet_u64();
                regs->r13 = nondet_u64();
                regs->r14 = nondet_u64();
                regs->r15 = nondet_u64();
            }

/*            #if !defined (__XMHF_VERIFICATION__)
            memcpy(oparams, & __xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
                   sizeof(x86regs64_t));
            #endif*/
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE:{
            //iparams = x86regs64_t *, oparams=NULL
/*            //checks:
            //1. iparams should be within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(x86regs64_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined(__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(x86regs64_t)));
            #endif // defined
*/

            //void

/*            #if !defined (__XMHF_VERIFICATION__)
            memcpy(& __xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
                   iparams,
                   sizeof(x86regs64_t));
            #endif
*/
        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_WRMSR:{
            //iparams = msr, oparams = value
/*            //checks
            //1. msr cannot contain any value that is specific to HIC
            if(!( iparams != MSR_EFER && iparams != IA32_SYSENTER_CS_MSR && iparams != IA32_SYSENTER_EIP_MSR && iparams != IA32_SYSENTER_ESP_MSR)){
                _XDPRINTF_("%s[%u],%u: uapierr: HIC specific iparams being written to. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined(__XMHF_VERIFICATION__)
            assert(( iparams != MSR_EFER && iparams != IA32_SYSENTER_CS_MSR && iparams != IA32_SYSENTER_EIP_MSR && iparams != IA32_SYSENTER_ESP_MSR));
            #endif // defined
*/
            //void

/*            #if !defined (__XMHF_VERIFICATION__)
            wrmsr64((u32)iparams, oparams);
            #endif
*/
        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_RDMSR:{
            //iparams = msr, oparams = (u64 *)
/*            //checks:
            //1. msr cannot contain any value that is specific to HIC
            if(!( iparams != MSR_EFER && iparams != IA32_SYSENTER_CS_MSR && iparams != IA32_SYSENTER_EIP_MSR && iparams != IA32_SYSENTER_ESP_MSR)){
                _XDPRINTF_("%s[%u],%u: uapierr: HIC specific MSR being read from. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined(__XMHF_VERIFICATION__)
            assert(( iparams != MSR_EFER && iparams != IA32_SYSENTER_CS_MSR && iparams != IA32_SYSENTER_EIP_MSR && iparams != IA32_SYSENTER_ESP_MSR));
            #endif // defined

            //2. oparams should be within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(u64))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined(__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(u64)));
            #endif // defined
*/
            {
                u64 value = nondet_u64();
                *(u64 *)oparams = value;
            }


/*            #if !defined (__XMHF_VERIFICATION__)
            *(u64 *)oparams = rdmsr64((u32)iparams);
            #endif
*/
        }
        break;

        default:
            _XDPRINTF_("%s[%u]: Unknown cpustate subcall %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_subnum);
            //HALT();
            return;
    }

}










//////
// physmem UAPI sub-handler
static void __xmhfhic_rtm_uapihandler_physmem(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid){
    //_XDPRINTF_("%s[%u]: Got control...\n", __FUNCTION__, (u32)cpuid);

    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_PHYSMEM_PEEK:{
            //iparams = (xmhf_hic_uapi_physmem_desc_t *), oparams = unused
/*            xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)iparams;


            //checks:
            //1. iparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_physmem_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: iparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }



            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_physmem_desc_t)));
            #endif // defined

            //2. destination slab is within bounds and is a guest slab
            if(! (pdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is out of bounds. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((pdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ));
            #endif // defined

            if( !(_x_xmhfhic_common_slab_info_table[pdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is not a guest slab. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((_x_xmhfhic_common_slab_info_table[pdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST));
            #endif // defined


            //3. pdesc->addr_from and pdesc->numbytes is within destination slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(pdesc->guest_slab_index, pdesc->addr_from, pdesc->numbytes)){
                _XDPRINTF_("%s[%u],%u: uapierr: addr_from is not within destination slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(pdesc->guest_slab_index, pdesc->addr_from, pdesc->numbytes));
            #endif // defined


            //4. pdesc->addr_to is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, pdesc->addr_to, pdesc->numbytes)){
                _XDPRINTF_("%s[%u],%u: uapierr: addr_to is not within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, pdesc->addr_to, pdesc->numbytes));
            #endif // defined

            #if !defined (__XMHF_VERIFICATION__)
            memcpy(pdesc->addr_to, pdesc->addr_from, pdesc->numbytes);
            #endif
*/
        }
        break;

        case XMHF_HIC_UAPI_PHYSMEM_POKE:{
/*            //iparams = (xmhf_hic_uapi_physmem_desc_t *), oparams = unused
            xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)iparams;

            //checks:
            //1. iparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_physmem_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: iparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_physmem_desc_t)));
            #endif // defined


            //2. destination slab is within bounds and is a guest slab
            if(! (pdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is out of bounds. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((pdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ));
            #endif // defined


            if( !(_x_xmhfhic_common_slab_info_table[pdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is not a guest slab. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((_x_xmhfhic_common_slab_info_table[pdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST));
            #endif // defined

            //3. pdesc->addr_to and pdesc->numbytes is within destination slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(pdesc->guest_slab_index, pdesc->addr_to, pdesc->numbytes)){
                _XDPRINTF_("%s[%u],%u: uapierr: addr_to is not within destination slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(pdesc->guest_slab_index, pdesc->addr_to, pdesc->numbytes));
            #endif // defined


            //4. pdesc->addr_from is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, pdesc->addr_from, pdesc->numbytes)){
                _XDPRINTF_("%s[%u],%u: uapierr: addr_to is not within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, pdesc->addr_from, pdesc->numbytes));
            #endif // defined

            #if !defined (__XMHF_VERIFICATION__)
            memcpy(pdesc->addr_to, pdesc->addr_from, pdesc->numbytes);
            #endif
*/
        }
        break;


        default:
            _XDPRINTF_("%s[%u]: Unknown physmem subcall %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_subnum);
            //HALT();
            return;

    }

}









//////
// mempgtbl UAPI sub-handler
static void __xmhfhic_rtm_uapihandler_mempgtbl(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid, u64 src_slabid){
    //_XDPRINTF_("%s[%u]: Got control...\n", __FUNCTION__, (u32)cpuid);

    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_MEMPGTBL_GETENTRY:{
/*            //iparams = xmhf_hic_uapi_mempgtbl_desc_t *; oparams = xmhf_hic_uapi_mempgtbl_desc_t *
            xmhf_hic_uapi_mempgtbl_desc_t *imdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)iparams;
            xmhf_hic_uapi_mempgtbl_desc_t *omdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)oparams;

            //checks:
            //1. iparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: iparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t)) );
            #endif // defined

            //2. oparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: oparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert(_uapicheck_is_within_slab_memory_extents(src_slabid, oparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t)) );
            #endif // defined

            //3. destination slab is within bounds and is a guest slab
            if(! (imdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is out of bounds. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((imdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ));
            #endif // defined


            if( !(_x_xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is not a guest slab. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((_x_xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST));
            #endif // defined

            //u64 pdpt_index = pae_get_pdpt_index(imdesc->gpa);
            //u64 pd_index = pae_get_pdt_index(imdesc->gpa);
            //u64 pt_index = pae_get_pt_index(imdesc->gpa);
            u64 pt_index = imdesc->gpa/PAGE_SIZE_4K;

            //checks:
            //4. iparams->gpa fits within destination slab mempgtbl extents (pdpt_index, pd_index and pt_index bounds)
            if( !(pt_index < 1048576) ){
                _XDPRINTF_("%s[%u],%u: uapierr: mempgtbl indices out of bound. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert((pt_index < 1048576));
            #endif // defined
*/

            {
                u64 value=nondet_u64();
                omdesc->entry = value;
            }


/*            {
                u64 *table = (u64 *)_x_xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.mempgtbl_pt;
                omdesc->entry = table[pt_index];
            }
*/
        }
        break;


        case XMHF_HIC_UAPI_MEMPGTBL_SETENTRY:{
/*            //iparams = xmhf_hic_uapi_mempgtbl_desc_t *; oparams = unused
            xmhf_hic_uapi_mempgtbl_desc_t *imdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)iparams;


            //checks:
            //1. iparams is within source slab memory extents
            if(!_uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t))){
                _XDPRINTF_("%s[%u],%u: uapierr: iparams should be within source slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert( _uapicheck_is_within_slab_memory_extents(src_slabid, iparams, sizeof(xmhf_hic_uapi_mempgtbl_desc_t)) );
            #endif // defined


            //2. destination slab is within bounds and is a guest slab
            if(! (imdesc->guest_slab_index < XMHF_HIC_MAX_SLABS ) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is out of bounds. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert( imdesc->guest_slab_index < XMHF_HIC_MAX_SLABS );
            #endif // defined


            if( !(_x_xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST) ){
                _XDPRINTF_("%s[%u],%u: uapierr: destination slab is not a guest slab. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert( _x_xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.slabtype == HIC_SLAB_X86VMXX86PC_GUEST );
            #endif // defined

            //u64 pdpt_index = pae_get_pdpt_index(imdesc->gpa);
            //u64 pd_index = pae_get_pdt_index(imdesc->gpa);
            //u64 pt_index = pae_get_pt_index(imdesc->gpa);
            u64 pt_index = imdesc->gpa/PAGE_SIZE_4K;

            //checks:
            //3. iparams->gpa fits within destination slab mempgtbl extents (pdpt_index, pd_index and pt_index bounds)
            if( !(pt_index < 1048576) ){
                _XDPRINTF_("%s[%u],%u: uapierr: mempgtbl indices out of bound. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                //HALT();
                return;
            }

            #if defined (__XMHF_VERIFICATION__)
            assert( (pt_index < 1048576) );
            #endif // defined

            //4. if iparams->entry has present bit set then entry is within destination slab memory extents
            if( imdesc->entry & 0x7 ){
                if(!_uapicheck_is_within_slab_memory_extents(imdesc->guest_slab_index, (imdesc->entry & 0xFFFFFFFFFFFFF000UL), 1)){
                    _XDPRINTF_("%s[%u],%u: uapierr: mempgtbl entry is not within destination slab memory extents. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
                    //HALT();
                    return;
                }

                #if defined (__XMHF_VERIFICATION__)
                assert( _uapicheck_is_within_slab_memory_extents(imdesc->guest_slab_index, (imdesc->entry & 0xFFFFFFFFFFFFF000UL), 1) );
                #endif // defined
            }
*/



/*            {
                u64 *table = (u64 *)_x_xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.mempgtbl_pt;
                table[pt_index] = imdesc->entry;
            }

            //#if defined (__XMHF_VERIFICATION__)
            //assert(0);
            //#endif //__XMHF_VERIFICATION__
*/

        }
        break;


        default:
            _XDPRINTF_("%s[%u]: Unknown cpustate subcall %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_subnum);
            return;

    }

}


