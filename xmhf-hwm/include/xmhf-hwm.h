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


//XMHF hardware interface
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_HWM_H__
#define __XMHF_HWM_H__

#define __CASMFNDEF__(x) __attribute__((naked))
#define __CASMFNCALL__(x) (x);


#if defined(__XMHF_TARGET_TRIAD_X86_VMX_X86PC__)

#ifndef __ASSEMBLY__
	typedef struct {
		u32 addr_start;
		u32 addr_end;
		u32 protection;
	} physmem_extent_t;

	typedef enum {
		SYSMEMREADU8,
		SYSMEMREADU16,
		SYSMEMREADU32,
		SYSMEMREADU64
	} sysmem_read_t;

	typedef enum {
		SYSMEMWRITEU8,
		SYSMEMWRITEU16,
		SYSMEMWRITEU32,
		SYSMEMWRITEU64
	} sysmem_write_t;


#endif // __ASSEMBLY__

    #include <xmhfhwm_casm.h>  			//CPU
    #include <xmhfhwm_cpu.h>  			//CPU
    #include <xmhfhwm_pci.h>        		//PCI bus glue
    #include <xmhfhwm_pit.h>        		//PIT
    #include <xmhfhwm_vtd.h>			//VMX DMA protection
    #include <xmhfhwm_lapic.h>			//APIC
    #include <xmhfhwm_bios.h>			//ACPI glue
    #include <xmhfhwm_e1000.h>			//e1000 network card

#else

	#error "You must define a valid cpu-container-platform triad before trying to build."

#endif


#endif //__XMHF_HWM_H__
