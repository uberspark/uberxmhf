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

#include <xcguestslab.h>

//////
XMHF_SLAB_GUEST(xcguestslab)



/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


static void xcguestslab_dotest_vmcall(void){

    {
        u64 tscbefore, tscafter, tscavg=0;
        u32 iterations=8192;
        u32 i;

        _XDPRINTF_("%s: proceeding with test...\n", __FUNCTION__);



        for(i=0; i < iterations; i++){
            tscbefore = rdtsc64();

            {

                //asm volatile ("vmcall \r\n");

            }

            tscafter = rdtsc64();
            tscavg += (tscafter - tscbefore);
        }

        tscavg = tscavg / iterations;

        _XDPRINTF_("%s: clock cycles for test = %u\n", __FUNCTION__, (u32)tscavg);

    }



}


static void xcguestslab_do_vmcall(void){
    u64 magic = 0xAABBCCDDAABBCCDDULL;

    _XDPRINTF_("%s: Going for VMCALL, magic=%016llx\n",
                __FUNCTION__, magic);

    asm volatile(
        "movq %0, %%rax \r\n"
        "vmcall \r\n"
        "movq %%rax, %0 \r\n"
        :
        : "m" (magic)
        : "rax"
    );

    _XDPRINTF_("%s: Came back from VMCALL, magic=%016llx\n",
                __FUNCTION__, magic);


}


static void xcguestslab_do_cpuid(void){
    u32 dummy;
    u32 vendor_dword1, vendor_dword2, vendor_dword3;


    _XDPRINTF_("%s: Preparing to execute CPUID...\n",
                __FUNCTION__);

    cpuid(0, &dummy, &vendor_dword1, &vendor_dword3, &vendor_dword2);

    _XDPRINTF_("%s: CPUID(0) %x, %x, %x\n",
                __FUNCTION__, vendor_dword1, vendor_dword2, vendor_dword3);
}

void xcguestslab_interface(void) {
    _XDPRINTF_("%s: Hello world from Guest slab!\n", __FUNCTION__);

    //xcguestslab_dotest_vmcall();

    //xcguestslab_do_vmcall();

    xcguestslab_do_cpuid();

    _XDPRINTF_("%s: Guest Slab Halting\n", __FUNCTION__);
    HALT();
}

