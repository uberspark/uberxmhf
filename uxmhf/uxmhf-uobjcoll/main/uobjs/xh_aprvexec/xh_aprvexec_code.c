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

// aprvexec hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_gcpustate.h>
//#include <uapi_slabmemacc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_slabmempgtbl.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xh_aprvexec.h>



#define APRVEXEC_LOCK     			0xD0
#define APRVEXEC_UNLOCK   			0xD1

static uint8_t _ae_page_buffer[PAGE_SIZE_4K];

static uint8_t _ae_database[][SHA_DIGEST_LENGTH] = {
  {0xd1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x74, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xa1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x71, 0x74, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xf1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x54, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xe1, 0x4e, 0x30, 0x25,  0x9e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x74, 0x78, 0x6b, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0x88, 0x3a, 0x97, 0x59,  0x09,  0x80, 0x12, 0xa9, 0x3b, 0xfb, 0x38, 0x09, 0xb2, 0xf2, 0xca, 0xb6, 0x12, 0x8c, 0x64, 0x52},
  {0x9d, 0xe8, 0x61, 0x2a,  0xea,  0x00, 0xc7, 0xe7, 0x8f, 0xd5, 0xf3, 0x6f, 0x7d, 0xec, 0xff, 0xda, 0xf9, 0xd9, 0xf9, 0x2f},
};

#define NUMENTRIES_AE_DATABASE  (sizeof(_ae_database)/sizeof(_ae_database[0]))


//approve and lock a page (at gpa)
static void ae_lock(uint32_t cpuindex, uint32_t guest_slab_index, uint64_t gpa){
    slab_params_t spl;
    //xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&spl.in_out_params[2];
    //xmhf_uapi_slabmemacc_params_t *smemaccp = (xmhf_uapi_slabmemacc_params_t *)spl.in_out_params;
    uint8_t digest[SHA_DIGEST_LENGTH];
    bool found_in_database=false;
    uint32_t i;

    _XDPRINTF_("%s[%u]: starting...\n", __func__, (uint16_t)cpuindex);
    spl.src_slabid = XMHFGEEC_SLAB_XH_APRVEXEC;
    //spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMACC;
    spl.cpuid = cpuindex;

if(!ae_activated){
    //grab page contents at gpa into local page buffer
    //smemaccp->dst_slabid = guest_slab_index;
    //smemaccp->addr_to = &_ae_page_buffer;
    //smemaccp->addr_from = gpa;
    //smemaccp->numbytes = PAGE_SIZE_4K;
    ////spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;
    // spl.dst_uapifn = XMHF_HIC_UAPI_PHYSMEM_PEEK;
    //XMHF_SLAB_CALLNEW(&spl);
    CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmemaccess_copy, &_ae_page_buffer, gpa,
		PAGE_SIZE_4K);

    _XDPRINTF_("%s[%u]: grabbed page contents at gpa=%016x\n",
                __func__, (uint16_t)cpuindex, gpa);

    _XDPRINTF_("%s[%u]: %02x, %02x, %02x, %02x, %02x ...\n",
                __func__, (uint16_t)cpuindex, _ae_page_buffer[0], _ae_page_buffer[1],
				_ae_page_buffer[2], _ae_page_buffer[3], _ae_page_buffer[4]);

    //compute SHA-1 of the local page buffer
    unsigned long outlen = 20; // not sure what outlen is for, placeholder for now...
    uberspark_uobjrtl_crypto__hashes_sha1__sha1_memory(&_ae_page_buffer, PAGE_SIZE_4K, digest, &outlen);

    _XDPRINTF_("%s[%u]: computed SHA-1: %*D\n",
               __func__, (uint16_t)cpuindex, SHA_DIGEST_LENGTH, digest, " ");

    //compare computed SHA-1 to the database
    for(i=0; i < NUMENTRIES_AE_DATABASE; i++){
        if(!uberspark_uobjrtl_crt__memcmp(&digest, &_ae_database[i], SHA_DIGEST_LENGTH)){
            found_in_database=true;
            break;
        }
    }

    //if not approved then just return
    if(!found_in_database){
        _XDPRINTF_("%s[%u]: could not find entry in database. returning\n",
               __func__, (uint16_t)cpuindex);
        return;
    }

    _XDPRINTF_("%s[%u]: entry matched in database, proceeding to lock page...\n",
               __func__, (uint16_t)cpuindex);

    {
        //lock the code page so no one can write to it
        //xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];
        //xmhf_uapi_slabmempgtbl_entry_params_t *smpgtblep =
        //    (xmhf_uapi_slabmempgtbl_entry_params_t *)spl.in_out_params;
            xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t *flushtlbp =
        (xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t *)spl.in_out_params;


        spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;

         spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR;
        getentryforpaddrp->dst_slabid = guest_slab_index;
        getentryforpaddrp->gpa = gpa;
        XMHF_SLAB_CALLNEW(&spl);
        _XDPRINTF_("%s[%u]: original entry for gpa=%016llx is %016llx\n",
                   __func__, (uint16_t)cpuindex, gpa, getentryforpaddrp->result_entry);

         spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = guest_slab_index;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = (getentryforpaddrp->result_entry & ~(0x7));
        setentryforpaddrp->entry |= 0x5; // execute, read-only
        XMHF_SLAB_CALLNEW(&spl);


        //flush EPT TLB for permission changes to take effect
		spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_FLUSHTLB;
		flushtlbp->dst_slabid = guest_slab_index;
		XMHF_SLAB_CALLNEW(&spl);


		/*
        //////
        //debug
        //////
        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR;
        getentryforpaddrp->dst_slabid = guest_slab_index;
        getentryforpaddrp->gpa = gpa;
        XMHF_SLAB_CALLNEW(&spl);
       _XDPRINTF_("%s[%u]: new entry for gpa=%016llx is %016llx\n",
                  __func__, (uint16_t)cpuindex, gpa, getentryforpaddrp->result_entry);

        //////
*/

        ae_activated = true;
        ae_paddr = (uint32_t)gpa;
        _XDPRINTF_("%s[%u]: approved and locked page at gpa %x\n",
                   __func__, (uint16_t)cpuindex, gpa);
    }
}

}


//unlock a page (at gpa)
static void ae_unlock(uint32_t cpuindex, uint32_t guest_slab_index, uint64_t gpa){
     slab_params_t spl;
     //xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];
    //xmhf_uapi_slabmempgtbl_entry_params_t *smpgtblep =
    //    (xmhf_uapi_slabmempgtbl_entry_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;


     spl.src_slabid = XMHFGEEC_SLAB_XH_APRVEXEC;
     spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
     spl.cpuid = cpuindex;
     //spl.in_out_params[0] = XMHF_HIC_UAPI_MEMPGTBL;

    _XDPRINTF_("%s[%u]: starting...\n", __func__, (uint16_t)cpuindex);

    if(ae_activated){
         //unlock the code page
         spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR;
        getentryforpaddrp->dst_slabid = guest_slab_index;
        getentryforpaddrp->gpa = gpa;
         XMHF_SLAB_CALLNEW(&spl);

         _XDPRINTF_("%s[%u]: original entry for gpa=%016llx is %016llx\n",
                    __func__, (uint16_t)cpuindex, gpa, getentryforpaddrp->result_entry);

         spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = guest_slab_index;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = getentryforpaddrp->result_entry & ~(0x7);
        setentryforpaddrp->entry |= 0x7; // execute, read-write
        XMHF_SLAB_CALLNEW(&spl);

        ae_activated=false;
        ae_paddr=0;
        _XDPRINTF_("%s[%u]: restored permissions for page at %016llx\n",
                   __func__, (uint16_t)cpuindex, gpa);
    }
}



//////
// hypapp callbacks


//initialization
static void _hcb_initialize(uint32_t cpuindex){
	_XDPRINTF_("%s[%u]: aprvexec initializing...\n", __func__, (uint16_t)cpuindex);
}

//hypercall
static void _hcb_hypercall(uint64_t cpuindex, uint64_t guest_slab_index){
    slab_params_t spl;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    x86regs_t *gprs = (x86regs_t *)&gcpustate_gprs->gprs;
	uint32_t call_id;
	uint64_t gpa;

    spl.src_slabid = XMHFGEEC_SLAB_XH_APRVEXEC;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_CALLNEW(&spl);


    call_id = gprs->eax;
    gpa = ((uint64_t)gprs->ebx << 32) | gprs->edx;



	switch(call_id){

		case APRVEXEC_LOCK:{
		    _XDPRINTF_("%s[%u]: call_id=%x(LOCK), eax=%08x,ebx=%08x,edx=%08x\n",
		               __func__, (uint16_t)cpuindex, call_id, gprs->eax, gprs->ebx, gprs->edx);
			_XDPRINTF_("%s[%u]: call_id=%x(LOCK), gpa=%016llx\n", __func__, (uint16_t)cpuindex, call_id, gpa);
		    ae_lock(cpuindex, guest_slab_index, gpa);
		}
		break;

		case APRVEXEC_UNLOCK:{
		    _XDPRINTF_("%s[%u]: call_id=%x(UNLOCK), eax=%08x,ebx=%08x,edx=%08x\n",
		               __func__, (uint16_t)cpuindex, call_id, gprs->eax, gprs->ebx, gprs->edx);
			_XDPRINTF_("%s[%u]: call_id=%x(UNLOCK), gpa=%016llx\n", __func__, (uint16_t)cpuindex, call_id, gpa);
			ae_unlock(cpuindex, guest_slab_index, gpa);
		}
		break;

		default:
            //_XDPRINTF_("%s[%u]: unsupported hypercall %x. Ignoring\n", __func__, (uint16_t)cpuindex, call_id);
			break;
	}

}


//memory fault
static void _hcb_memoryfault(uint32_t cpuindex, uint32_t guest_slab_index, uint64_t gpa, uint64_t gva, uint64_t errorcode){

    if(ae_activated && ae_paddr == (uint32_t)gpa){
    	_XDPRINTF_("%s[%u]: memory fault in guest slab %u; gpa=%016llx, gva=%016llx, errorcode=%016llx, write error to approved code. Halting!\n",
            __func__, (uint16_t)cpuindex, guest_slab_index, gpa, gva, errorcode);
    	HALT();
    }

}

// shutdown
static void _hcb_shutdown(uint32_t cpuindex, uint32_t guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n", __func__, (uint16_t)cpuindex, guest_slab_index);
}









//////
// slab interface

// slab_interface(slab_input_params_t *iparams, uint64_t iparams_size, slab_output_params_t *oparams, uint64_t oparams_size, uint64_t src_slabid, uint64_t cpuindex){
void xh_aprvexec_slab_main(slab_params_t *sp){
    //xc_hypappcb_inputparams_t *hcb_iparams = (xc_hypappcb_inputparams_t *)iparams;
    //xc_hypappcb_outputparams_t *hcb_oparams = (xc_hypappcb_outputparams_t *)oparams;
    xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&sp->in_out_params[0];
    hcbp->cbresult=XC_HYPAPPCB_CHAIN;

	//_XDPRINTF_("XHAPRVEXEC[%u]: Got control, cbtype=%x: ESP=%08x\n",
    //             (uint16_t)sp->cpuid, hcbp->cbtype, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_esp,CASM_NOPARAM));


    switch(hcbp->cbtype){
        case XC_HYPAPPCB_INITIALIZE:{
            _hcb_initialize(sp->cpuid);
        }
        break;

        case XC_HYPAPPCB_HYPERCALL:{
            _hcb_hypercall(sp->cpuid, hcbp->guest_slab_index);
        }
        break;

        case XC_HYPAPPCB_MEMORYFAULT:{
         	uint64_t errorcode;
         	uint64_t gpa;
         	uint64_t gva;
         	slab_params_t spl;
       	    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
                (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;


         	spl.src_slabid = XMHFGEEC_SLAB_XH_APRVEXEC;
         	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
         	spl.cpuid = sp->cpuid;
            //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;
             spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;

            gcpustate_vmrwp->encoding = VMCS_INFO_EXIT_QUALIFICATION;
            XMHF_SLAB_CALLNEW(&spl);
            errorcode = gcpustate_vmrwp->value;

            gcpustate_vmrwp->encoding = VMCS_INFO_GUEST_PADDR_FULL;
            XMHF_SLAB_CALLNEW(&spl);
            gpa = gcpustate_vmrwp->value;

            gcpustate_vmrwp->encoding = VMCS_INFO_GUEST_LINEAR_ADDRESS;
            XMHF_SLAB_CALLNEW(&spl);
            gva = gcpustate_vmrwp->value;

            _hcb_memoryfault(sp->cpuid, hcbp->guest_slab_index, gpa, gva, errorcode);
        }
        break;

        case XC_HYPAPPCB_SHUTDOWN:{
            _hcb_shutdown(sp->cpuid, hcbp->guest_slab_index);
        }
        break;

        //case XC_HYPAPPCB_TRAP_IO:{
        //
        //
        //}
        //break;

        //case XC_HYPAPPCB_TRAP_INSTRUCTION:{
        //
        //
        //}
        //break;

        //case XC_HYPAPPCB_TRAP_EXCEPTION:{
        //
        //
        //}
        //break;


        default:{
            //_XDPRINTF_("%s[%u]: Unknown cbtype. Ignoring!\n",
            //    __func__, (uint16_t)sp->cpuid);
        }
    }

}
