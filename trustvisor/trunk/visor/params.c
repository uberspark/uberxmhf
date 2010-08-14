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

#include <types.h>
#include <error.h>
#include <multiboot.h>
#include <string.h>
#include <print.h>
#include <svm.h>
#include <sha1.h>
#include <processor.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <io.h>
#include <pci.h>
#include <dev.h>
#include <params.h>

/*get the which(th) parameter value from stack*/
u32 pm_get_stack_param(u64 cr3, u32 rsp, u32 which)
{
	u32 data, addr;

	if (which < 1)
	{
		printf("scode DEBUG: parameter number error");
		return 0;
	}

	addr = rsp + 4*(which-1);
	data = get_32bit_aligned_value_from_guest(cr3, addr);
	return data;
}


/*memory copy from guest to guest, the data must be 32bit aligned*/
void pm_copy_guest_to_guest(u64 cr3, u32 src, u32 dst, u32 len)
{
	u32 i, ilen, data;
	u32 src_addr, dst_addr;
	u64 icr3;

	ilen = len;
	icr3 = cr3;
	src_addr = src;
	dst_addr = dst;

	for (i =0; i < ilen; i++)
	{
		data = get_32bit_aligned_value_from_guest(icr3, src_addr);
		put_32bit_aligned_value_to_guest(icr3, dst_addr, data);

		src_addr += 4;
		dst_addr += 4;
	}

}
