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

#include <xc.h>
#include <xc_nwlog.h>

/*
 * xcnwlog_logdata: log network log buffer to the network
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

//@ghost bool xcnwlog_logdata_invokepush = false;
//@ghost bool xcnwlog_logdata_copytodmaregion = false;
//@ghost bool xcnwlog_logdata_xmit = false;
//@ghost bool xcnwlog_logdata_resetbuffer = false;
/*@
	behavior logdata_xmitandresetbuffer:
		assumes (xcnwlog_ls_index[0] >= XC_NWLOG_BUF_MAXELEM);
		ensures (xcnwlog_logdata_invokepush == \at(xcnwlog_logdata_invokepush, Pre));
		ensures (xcnwlog_logdata_copytodmaregion == true);
		ensures (xcnwlog_logdata_xmit == true);
		ensures (xcnwlog_logdata_resetbuffer == true);
		ensures (xcnwlog_ls_index[0] == 0);

	behavior logdata_onlylog:
		assumes (xcnwlog_ls_index[0] < XC_NWLOG_BUF_MAXELEM);
		ensures (xcnwlog_logdata_invokepush == true);
		ensures (xcnwlog_logdata_copytodmaregion == \at(xcnwlog_logdata_copytodmaregion, Pre));
		ensures (xcnwlog_logdata_xmit == \at(xcnwlog_logdata_xmit, Pre));
		ensures (xcnwlog_logdata_resetbuffer == \at(xcnwlog_logdata_resetbuffer, Pre));
		ensures (xcnwlog_ls_index[0] == \at(xcnwlog_ls_index[0], Pre));

	complete behaviors;
	disjoint behaviors;

@*/

void xcnwlog_logdata(xcnwlog_ls_element_t elem){
	if(xcnwlog_ls_index[0] >= XC_NWLOG_BUF_MAXELEM){
		//memcpy(&xcnwlog_lsdma[0], &xcnwlog_ls[0], sizeof(xcnwlog_ls_element_t)*XC_NWLOG_BUF_MAXELEM);
		memcpy(&xcnwlog_packet.logbuf, &xcnwlog_ls[0], sizeof(xcnwlog_ls_element_t)*XC_NWLOG_BUF_MAXELEM);
		//@ghost xcnwlog_logdata_copytodmaregion = true;
		e1000_xmitack();
		//@ghost xcnwlog_logdata_xmit = true;
		memset(&xcnwlog_ls[0], 0, sizeof(xcnwlog_ls[0]));
		//@ghost xcnwlog_logdata_resetbuffer = true;
		xcnwlog_ls_index[0]=0;
	}else{
		xcnwlog_ls_push(0, elem);
		//@ghost xcnwlog_logdata_invokepush = true;
	}
}

