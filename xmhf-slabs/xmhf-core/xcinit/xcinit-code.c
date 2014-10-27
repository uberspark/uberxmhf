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

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xcinit.h>
#include <xctestslab1.h>

//////
XMHF_SLAB(xcinit)

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


static void _xcinit_dotests(u64 cpuid){

    {
        u64 tscbefore, tscafter, tscavg=0;
        u32 iterations=8192;
        u32 i;

        _XDPRINTF_("%s: proceeding with test...\n", __FUNCTION__);



        for(i=0; i < iterations; i++){
            tscbefore = rdtsc64();

            {

                //XMHF_SLAB_CALL(hictestslab2, XMHF_HYP_SLAB_HICTESTSLAB2, NULL, 0, NULL, 0);

            }

            tscafter = rdtsc64();
            tscavg += (tscafter - tscbefore);
        }

        tscavg = tscavg / iterations;

        _XDPRINTF_("%s: clock cycles for test = %u\n", __FUNCTION__, (u32)tscavg);

    }

}



void xcinit_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuid){
    bool isbsp = (cpuid & 0x8000000000000000ULL) ? true : false;
    u64 inputval, outputval;
    static u64 cpucount=0;
    static u32 __xcinit_smplock = 1;

	_XDPRINTF_("%s[%u]: Got control: RSP=%016llx\n",
                __FUNCTION__, (u32)cpuid, read_rsp());

    if(!isbsp){
        _XDPRINTF_("%s[%u]: AP Halting!\n",
                __FUNCTION__, (u32)cpuid);

        spin_lock(&__xcinit_smplock);
        cpucount++;
        spin_unlock(&__xcinit_smplock);

        HALT();
    }else{
        //BSP
        _XDPRINTF_("%s[%u]: BSP waiting to rally APs...\n",
                __FUNCTION__, (u32)cpuid);

        while(cpucount < (xcbootinfo->cpuinfo_numentries-1));

        _XDPRINTF_("%s[%u]: BSP, APs halted. Proceeding...\n",
                __FUNCTION__, (u32)cpuid);
    }


    //_XDPRINTF_("%s[%u]: iparams=%016llx, iparams_size=%u\n",
    //             __FUNCTION__, (u32)cpuid, iparams, iparams_size);

    //_XDPRINTF_("%s[%u]:  oparams=%016llx, oparams_size=%u\n",
    //             __FUNCTION__, (u32)cpuid, oparams, oparams_size);



    _XDPRINTF_("%s[%u]: Proceeding to call xcguestslab; RSP=%016llx\n",
        __FUNCTION__, (u32)cpuid, read_rsp());

    XMHF_SLAB_CALL(xcguestslab, XMHF_GUEST_SLAB_XCGUESTSLAB, NULL, 0, NULL, 0);




    _XDPRINTF_("%s[%u]: Should  never get here.Halting!\n",
        __FUNCTION__, (u32)cpuid);

    HALT();


    return;
}


#if 0


        /*_XDPRINTF_("%s[%u]: Proceeding to call xctestslab1 interface; RSP=%016llx\n",
                __FUNCTION__, (u32)cpuid, read_rsp());

        inputval = 0xAABB;
        XMHF_SLAB_CALL(xctestslab1, XMHF_HYP_SLAB_XCTESTSLAB1, &inputval, sizeof(inputval), &outputval, sizeof(outputval));

        _XDPRINTF_("%s[%u]: Came back to xcinit; RSP=%016llx\n",
                __FUNCTION__, (u32)cpuid, read_rsp());
        _XDPRINTF_("%s[%u]: outputval=%016llx\n",
                __FUNCTION__, (u32)cpuid, outputval);*/


        //_xcinit_dotests(cpuid);

        asm volatile ("int $0x03\r\n");






#endif // 0
