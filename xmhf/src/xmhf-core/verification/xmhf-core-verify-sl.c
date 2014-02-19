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

//----------------------------------------------------------------------
// xmhf-core-verify-sl.c
// XMHF core Secure Loader (SL) verification driver
// author: amit vasudevan (amitvasudevan@acm.org)
//----------------------------------------------------------------------
#include <xmhf.h>

extern struct _sl_parameter_block slpb;
u8 xmhf_rpb_start[sizeof(RPB)];
u8 _rpb_e820buffer[1280];
u8 _rpb_cpuinfobuffer[128];

void main(){
		//populate slpb
		slpb.magic = SL_PARAMETER_BLOCK_MAGIC;
		slpb.errorHandler = 0;
		slpb.isEarlyInit = 1;
		slpb.numE820Entries = 2;
		//slpb.memmapbuffer;
		slpb.numCPUEntries = 1;
		//slpb.cpuinfobuffer;
		slpb.runtime_size = (80*1024*1024);				//size of the runtime image
		slpb.runtime_osbootmodule_base = 0;				//guest OS bootmodule base
		slpb.runtime_osbootmodule_size = 512;			//guest OS bootmodule size
		slpb.runtime_appmodule_base=0;	
		slpb.runtime_appmodule_size=0;
		slpb.rdtsc_before_drtm=0;
		slpb.rdtsc_after_drtm=0;
		//slpb.uart_config;
		//slpb.cmdline;

		//setup RPB
		{
				RPB *rpb = (RPB *)&xmhf_rpb_start;
				rpb->XtVmmE820Buffer = (u32)&_rpb_e820buffer;
				rpb->XtVmmMPCpuinfoBuffer = (u32)&_rpb_cpuinfobuffer;
		}

		_xmhf_sl_entry();
		assert(1);
}
//----------------------------------------------------------------------
