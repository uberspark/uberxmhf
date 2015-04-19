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
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc_testslab.h>

//////
//XMHF_SLAB(xctestslab1)

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


/*
static u8 _ae_page_buffer_src[PAGE_SIZE_4K];

static u8 _ae_page_buffer[PAGE_SIZE_4K];

static void _xcinit_dotests(u64 cpuid){

    {
        u64 tscbefore, tscafter, tscavg=0;
        u32 iterations=128;
        u32 i;
        u8 digest[SHA_DIGEST_LENGTH];

        _XDPRINTF_("%s: proceeding with test...\n", __func__);



        for(i=0; i < iterations; i++){
            tscbefore = CASM_FUNCCALL(rdtsc64,);

            {

                //memcpy(_ae_page_buffer, &_ae_page_buffer_src, PAGE_SIZE_4K);
                //compute SHA-1 of the local page buffer
                sha1_buffer(&_ae_page_buffer, PAGE_SIZE_4K, digest);

                //XMHF_SLAB_CALL(hictestslab2, XMHF_HYP_SLAB_HICTESTSLAB2, NULL, 0, NULL, 0);

            }

            tscafter = CASM_FUNCCALL(rdtsc64,);
            tscavg += (tscafter - tscbefore);
        }

        tscavg = tscavg / iterations;

        _XDPRINTF_("%s: clock cycles for test = %u\n", __func__, (u32)tscavg);

    }

}*/


/*void slab_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuid){
    u64 *inputval = (u64 *)iparams;
    u64 *outputval = (u64 *)oparams;

	_XDPRINTF_("%s[%u]: Got control: RSP=%016llx\n",
                __func__, (u32)cpuid, CASM_FUNCCALL(read_rsp,));

	_XDPRINTF_("%s[%u]: inputval=%x\n",
                __func__, (u32)cpuid, *inputval);

    *outputval = 0xBBCCDDEE;

    return;
}*/


void slab_main(slab_params_t *sp){
    u32 inputval = sp->in_out_params[0];
    u32 *outputval = (u32 *)&sp->in_out_params[1];

	_XDPRINTF_("XC_TESTSLAB[%u]: Got control: ESP=%x\n",
                (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));


    CASM_FUNCCALL(_xc_testslab_int3, CASM_NOPARAM);

	_XDPRINTF_("XC_TESTSLAB[%u]: inputval=%x\n",
                (u16)sp->cpuid, inputval);

    *outputval = 0xBBCCDDEE;

    return;
}

