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
 * x86 memory regions implementation
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <xmhf.h>
#include <xmhf-hwm.h>

u8 xmhfhwm_mem_region_apbootstrap_dataseg[XMHFHWM_MEM_X86SMP_APBOOTSTRAP_DATASEG_SIZE];

static unsigned char *xmhfhwm_mem_memcpy(unsigned char *dst, const unsigned char *src, size_t n)
{
	const unsigned char *p = src;
	unsigned char *q = dst;

	while (n) {
		*q++ = *p++;
		n--;
	}

	return dst;
}


bool _impl_xmhfhwm_mem_read(u32 sysmemaddr, sysmem_read_t readsize, u64 *read_result){
	bool retval = false;

	if(sysmemaddr == (XMHFHWM_MEM_X86SMP_APBOOTSTRAP_DATASEG_BASE + 0)){
		//@assert (readsize == SYSMEMREADU32);
		*read_result = *((u32 *)((u32)&xmhfhwm_mem_region_apbootstrap_dataseg + 0));
		retval = true;

	} else if(sysmemaddr == (XMHFHWM_MEM_X86SMP_APBOOTSTRAP_DATASEG_BASE + 8)){
		//@assert (readsize == SYSMEMREADU32);
		*read_result = *((u32 *)((u32)&xmhfhwm_mem_region_apbootstrap_dataseg + 8));
		retval = true;

	} else if(sysmemaddr == (XMHFHWM_MEM_X86SMP_APBOOTSTRAP_DATASEG_BASE + 32)){
		//@assert (readsize == SYSMEMREADU32);
		*read_result = *((u32 *)((u32)&xmhfhwm_mem_region_apbootstrap_dataseg + 32));
		retval = true;

	} else {

	}

	return retval;
}

bool _impl_xmhfhwm_mem_write(u32 sysmemaddr, sysmem_write_t writesize, u64 write_value){
	bool retval = false;

	//if(sysmemaddr == ){
	//	//@assert writesize == SYSMEMWRITEU32;
	//	retval = true;
	//}

	return retval;
}


bool _impl_xmhfhwm_mem_sysmemcopy(sysmem_copy_t sysmemcopy_type,
				u32 dstaddr, u32 srcaddr, u32 size){
	bool retval = false;

	if(sysmemcopy_type == SYSMEMCOPYOBJ2SYS){
		//dstaddr = sysmem address space
		//srcaddr = object address space
                if(dstaddr >= XMHFHWM_MEM_X86SMP_APBOOTSTRAP_DATASEG_BASE &&
			(dstaddr+size-1) < (XMHFHWM_MEM_X86SMP_APBOOTSTRAP_DATASEG_BASE + XMHFHWM_MEM_X86SMP_APBOOTSTRAP_DATASEG_SIZE)){
                        //@assert \valid((u8 *)srcaddr + (0..(size-1)) );
                        xmhfhwm_mem_memcpy( ((u32)&xmhfhwm_mem_region_apbootstrap_dataseg+(dstaddr - XMHFHWM_MEM_X86SMP_APBOOTSTRAP_DATASEG_BASE)),
					srcaddr, size);
                        retval = true;

		}else if(dstaddr >= XMHFHWM_MEM_X86SMP_APBOOTSTRAP_CODESEG_BASE &&
			(dstaddr+size-1) < (XMHFHWM_MEM_X86SMP_APBOOTSTRAP_CODESEG_BASE + XMHFHWM_MEM_X86SMP_APBOOTSTRAP_CODESEG_SIZE)){
			xmhfhwm_vdriver_mem_copy_to_apbootstrap_codeseg(srcaddr);
                        retval = true;

		}else{
			//we don't know about this region, so just return
		}
	}

	return retval;
}

