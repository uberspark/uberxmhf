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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc_nwlog.h>

/*
 * xcnwlog_addtolog: add data to network log
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


/*@
	requires nwlogValid (nwlog_id);

	assigns xcnwlog_ls_index[nwlog_id];
	assigns xcnwlog_ls[nwlog_id][xcnwlog_ls_index[nwlog_id]];

	behavior not_full:
		assumes !nwlogFull(nwlog_id);

		assigns xcnwlog_ls_index[nwlog_id];
		assigns xcnwlog_ls[nwlog_id][xcnwlog_ls_index[nwlog_id]];

		ensures H:nwlogValid (nwlog_id);
		ensures I:nwlogSize (nwlog_id) == nwlogSize {Old}(nwlog_id) + 1;
		ensures K:nwlogUnchanged {Pre ,Here }(nwlogStorage (nwlog_id), 0, nwlogSize{Pre}(nwlog_id));
		ensures J:nwlogTop( nwlogStorage (nwlog_id), nwlogSize{Pre}(nwlog_id), elem);
		ensures !nwlogEmpty (nwlog_id);
		ensures nwlogStorage (nwlog_id) == nwlogStorage {Old }( nwlog_id) ;
		ensures nwlogCapacity ( nwlog_id) == nwlogCapacity { Old }(nwlog_id) ;

	behavior full :
		assumes nwlogFull ( nwlog_id);

		assigns \nothing;

		ensures nwlogValid (nwlog_id);
		ensures nwlogFull ( nwlog_id);
		ensures nwlogUnchanged {Pre ,Here }(nwlogStorage (nwlog_id ), 0, nwlogSize(nwlog_id));
		ensures nwlogSize ( nwlog_id ) == nwlogSize { Old }(nwlog_id) ;
		ensures nwlogStorage (nwlog_id ) == nwlogStorage {Old }( nwlog_id) ;
		ensures nwlogCapacity ( nwlog_id ) == nwlogCapacity { Old }(nwlog_id) ;

	complete behaviors ;
	disjoint behaviors ;
*/
void xcnwlog_ls_push(uint32_t nwlog_id, xcnwlog_ls_element_t elem)
{
    uint32_t log_index =  xcnwlog_ls_index[nwlog_id];
    if(log_index >=0 && log_index < XC_NWLOG_BUF_MAXELEM) {
        xcnwlog_ls[nwlog_id][log_index].logbuf[0] = elem.logbuf[0];
        xcnwlog_ls[nwlog_id][log_index].logbuf[1] = elem.logbuf[1];
        xcnwlog_ls[nwlog_id][log_index].logbuf[2] = elem.logbuf[2];
        xcnwlog_ls[nwlog_id][log_index].logbuf[3] = elem.logbuf[3];
        xcnwlog_ls[nwlog_id][log_index].logbuf[4] = elem.logbuf[4];
        xcnwlog_ls[nwlog_id][log_index].logbuf[5] = elem.logbuf[5];
        xcnwlog_ls[nwlog_id][log_index].logbuf[6] = elem.logbuf[6];
        xcnwlog_ls[nwlog_id][log_index].logbuf[7] = elem.logbuf[7];
        xcnwlog_ls[nwlog_id][log_index].logbuf[8] = elem.logbuf[8];
        xcnwlog_ls[nwlog_id][log_index].logbuf[9] = elem.logbuf[9];
        xcnwlog_ls[nwlog_id][log_index].logbuf[10] = elem.logbuf[10];
        xcnwlog_ls[nwlog_id][log_index].logbuf[11] = elem.logbuf[11];
        xcnwlog_ls[nwlog_id][log_index].logbuf[12] = elem.logbuf[12];
        xcnwlog_ls[nwlog_id][log_index].logbuf[13] = elem.logbuf[13];
        xcnwlog_ls[nwlog_id][log_index].logbuf[14] = elem.logbuf[14];
        xcnwlog_ls[nwlog_id][log_index].logbuf[15] = elem.logbuf[15];

        log_index++;
        xcnwlog_ls_index[nwlog_id] = log_index;
    }
}

