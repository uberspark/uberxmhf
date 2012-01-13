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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

// EMHF secure loader component declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_SL_H__
#define __EMHF_SL_H__


#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//exported DATA 
extern u32 sl_baseaddr;	


//----------------------------------------------------------------------
//exported FUNCTIONS 


//----------------------------------------------------------------------
// arch. interfaces (GENERIC)
void* hva2sla(uintptr_t x);
u64 sla2spa(void* x);
bool sl_integrity_check(u8* runtime_base_addr, size_t runtime_len);
void sanitize_post_launch(void);
void early_dmaprot_init(u32 runtime_size);
void sl_xfer_control_to_runtime(RPB * rpb);

//----------------------------------------------------------------------
// arch. interfaces (SUBARCH SPECIFIC)

//protected DMA-protection buffer for early DMA protection (currently
// used by the x86 AMD arch. backend
extern u32 g_sl_protected_dmabuffer[];

void runtime_setup_paging(RPB * rpb, u32 runtime_spa, u32 runtime_sva, u32 totalsize);
void XtLdrTransferControlToRtm(u32 gdtbase, u32 idtbase,
	u32 entrypoint, u32 stacktop)__attribute__((cdecl)); 



#endif	//__ASSEMBLY__

#endif //__EMHF_DMAPROT_H__
