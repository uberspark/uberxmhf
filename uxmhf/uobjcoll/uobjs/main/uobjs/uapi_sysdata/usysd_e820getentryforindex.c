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
 * sysdata (E820) state uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/uapi_sysdata.h>


/*@
	requires \valid(gentryp);

	behavior returnentry:
		assumes (usysd_memmapinfo_maxindex <= MAX_E820_ENTRIES && gentryp->index < usysd_memmapinfo_maxindex);
		assigns	gentryp->baseaddr_high;
		assigns	gentryp->baseaddr_low;
		assigns gentryp->length_high;
		assigns gentryp->length_low;
		assigns gentryp->type;

	behavior invalid:
		assumes !(usysd_memmapinfo_maxindex <= MAX_E820_ENTRIES && gentryp->index < usysd_memmapinfo_maxindex);
		assigns \nothing;
@*/
void usysd_e820getentryforindex(uxmhf_uapi_sysdata_e820getentryforindex_t *gentryp){

	if(usysd_memmapinfo_maxindex <= MAX_E820_ENTRIES && gentryp->index < usysd_memmapinfo_maxindex){
		gentryp->baseaddr_high = usysd_memmapinfo[gentryp->index].baseaddr_high;
		gentryp->baseaddr_low = usysd_memmapinfo[gentryp->index].baseaddr_low;
		gentryp->length_high = usysd_memmapinfo[gentryp->index].length_high;
		gentryp->length_low = usysd_memmapinfo[gentryp->index].length_low;
		gentryp->type = usysd_memmapinfo[gentryp->index].type;
	}else{
		//invalid index, so return nothing
	}

}


