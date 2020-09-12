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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_sysdata.h>

/*@
	requires \valid(e820entryp);

	behavior addentry:
		assumes (usysd_memmapinfo_maxindex < MAX_E820_ENTRIES);
		assigns	usysd_memmapinfo[usysd_memmapinfo_maxindex];
		assigns usysd_memmapinfo_maxindex;
		ensures (usysd_memmapinfo_maxindex <= MAX_E820_ENTRIES);

	behavior invalid:
		assumes (usysd_memmapinfo_maxindex == MAX_E820_ENTRIES);
		assigns \nothing;
		ensures (usysd_memmapinfo_maxindex == MAX_E820_ENTRIES);
@*/
void usysd_e820addentry(uxmhf_uapi_sysdata_e820addentry_t *e820entryp){

		if(usysd_memmapinfo_maxindex < MAX_E820_ENTRIES){
			usysd_memmapinfo[usysd_memmapinfo_maxindex].baseaddr_high = e820entryp->baseaddr_high;
			usysd_memmapinfo[usysd_memmapinfo_maxindex].baseaddr_low = e820entryp->baseaddr_low;
			usysd_memmapinfo[usysd_memmapinfo_maxindex].length_high = e820entryp->length_high;
			usysd_memmapinfo[usysd_memmapinfo_maxindex].length_low = e820entryp->length_low;
			usysd_memmapinfo[usysd_memmapinfo_maxindex].type = e820entryp->type;
			usysd_memmapinfo_maxindex++;
		}else{
			//we have reached the max. permissible entries; no more additions
		}

}


