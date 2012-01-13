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

//libemhf.c - EMHF application inteface definitions
//author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <emhf.h> 

//==============================================================================
//exported interfaces

//---IOPM Bitmap interface------------------------------------------------------
void emhf_iopm_set_write(VCPU *vcpu, u32 port, u32 size){
  ASSERT(g_libemhf != NULL);
	return g_libemhf->emhf_iopm_set_write(vcpu, port, size);
}

//---MSRPM Bitmap interface------------------------------------------------------
void emhf_msrpm_set_write(VCPU *vcpu, u32 msr){
  ASSERT(g_libemhf != NULL);
	return g_libemhf->emhf_msrpm_set_write(vcpu, msr);
}

//---hardware pagetable flush-all routine---------------------------------------
void emhf_hwpgtbl_flushall(VCPU *vcpu){
  ASSERT(g_libemhf != NULL);
	return g_libemhf->emhf_hwpgtbl_flushall(vcpu);
}

//---hardware pagetable protection manipulation routine-------------------------
void emhf_hwpgtbl_setprot(VCPU *vcpu, u64 gpa, u64 flags){
  ASSERT(g_libemhf != NULL);
	return g_libemhf->emhf_hwpgtbl_setprot(vcpu, gpa, flags);
}

void emhf_hwpgtbl_setentry(VCPU *vcpu, u64 gpa, u64 value){
  ASSERT(g_libemhf != NULL);
	return g_libemhf->emhf_hwpgtbl_setentry(vcpu, gpa, value);
}


u64 emhf_hwpgtbl_getprot(VCPU *vcpu, u64 gpa){
  ASSERT(g_libemhf != NULL);
	return g_libemhf->emhf_hwpgtbl_getprot(vcpu, gpa);
}

/*
//---guest page-table walker, returns guest physical address--------------------
//note: returns 0xFFFFFFFF if there is no mapping
u8 * emhf_guestpgtbl_walk(VCPU *vcpu, u32 vaddr){
  ASSERT(g_libemhf != NULL);
	return g_libemhf->emhf_guestpgtbl_walk(vcpu, vaddr);
}*/


//---reboot functionality-------------------------------------------------------
void emhf_reboot(VCPU *vcpu){
  ASSERT(g_libemhf != NULL);
	return g_libemhf->emhf_reboot(vcpu);
}

