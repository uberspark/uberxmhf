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

// XMHF base platform component
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_BASEPLATFORM_H__
#define __XMHF_BASEPLATFORM_H__

//bring in arch. specific declarations
#include <arch/xmhf-baseplatform-arch.h>


#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//the master-id table, which is used by the AP bootstrap code
//to locate its own vcpu structure
//NOTE: The size of this structure _MUST_ be _EXACTLY_EQUAL_ to 8 bytes
//as it is made use of in low-level assembly language stubs
typedef struct _midtab {
    union {
        u32 cpu_lapic_id;       // CPU LAPIC id (unique)
        hva_t _cpu_lapic_id_64; // Keep struct aligned in amd64; don't use this
    };
    hva_t vcpu_vaddr_ptr;   // virt. addr. pointer to vcpu struct for this CPU
} __attribute__((packed)) MIDTAB;

#define SIZE_STRUCT_MIDTAB  (sizeof(struct _midtab))

//---platform
typedef struct _grube820 {
  u32 baseaddr_low;
  u32 baseaddr_high;
  u32 length_low;
  u32 length_high;
  u32 type;
} __attribute__((packed)) GRUBE820;

#define SIZE_STRUCT_GRUBE820  (sizeof(struct _grube820))

//---platform
typedef struct _pcpu {
  u32 lapic_id;
  u32 lapic_ver;
  u32 lapic_base;
  u32 isbsp;
} __attribute__((packed)) PCPU;

#define SIZE_STRUCT_PCPU  (sizeof(struct _pcpu))

//----------------------------------------------------------------------
//exported DATA
//----------------------------------------------------------------------
//system e820 map
	extern GRUBE820 g_e820map[] __attribute__(( section(".data") ));

//SMP CPU map; lapic id, base, ver and bsp indication for each available core
extern PCPU	g_cpumap[] __attribute__(( section(".data") ));

//runtime stacks for individual cores
extern u8 g_cpustacks[] __attribute__(( section(".bss.stack") ));

//VCPU structure for each "guest OS" core
extern VCPU g_vcpubuffers[] __attribute__(( section(".data") ));

//master id table, contains core lapic id to VCPU mapping information
extern MIDTAB g_midtable[] __attribute__(( section(".data") ));

//number of entries in the master id table, in essence the number of
//physical cores in the system
extern u32 g_midtable_numentries __attribute__(( section(".data") ));

//variable that is incremented by 1 by all cores that boot up, this should
//be finally equal to g_midtable_numentries at runtime which signifies
//that all physical cores have been booted up and initialized by the runtime
extern volatile u32 g_cpus_active __attribute__(( section(".data") ));

//SMP lock for the above variable
extern volatile u32 g_lock_cpus_active __attribute__(( section(".data") ));

//variable that is set to 1 by the BSP after rallying all the other cores.
//this is used by the application cores to enter the "wait-for-SIPI" state
extern volatile u32 g_ap_go_signal __attribute__(( section(".data") ));

//SMP lock for the above variable
extern volatile u32 g_lock_ap_go_signal __attribute__(( section(".data") ));

//----------------------------------------------------------------------
//exported FUNCTIONS
//----------------------------------------------------------------------

//get CPU vendor
u32 xmhf_baseplatform_getcpuvendor(void);

//initialize CPU state
void xmhf_baseplatform_cpuinitialize(void);

//initialize SMP
void xmhf_baseplatform_smpinitialize(void);

//initialize basic platform elements
void xmhf_baseplatform_initialize(void);

//reboot platform
void xmhf_baseplatform_reboot(VCPU *vcpu);

// Traverse the E820 map and return the base and limit of used system physical address (i.e., used by main memory and MMIO).
// [NOTE] <machine_high_spa> must be u64 even on 32-bit machines, because it could be 4G, and hence overflow u32.
// Return: <machine_base_spa> and <machine_limit_spa> may not be 4K-aligned.
// [TODO][Issue 85] Move this function to a better place
extern bool xmhf_baseplatform_x86_e820_paddr_range(spa_t* machine_base_spa, spa_t* machine_limit_spa);

#ifndef __XMHF_VERIFICATION__

	//hypervisor runtime virtual address to secure loader address
	//note: secure loader runs in a DS relative addressing mode and
	//rest of hypervisor runtime is at secure loader base address + 2MB
	static inline void * hva2sla(void *hva){
		return (void*)((hva_t)hva - rpb->XtVmmRuntimePhysBase + PAGE_SIZE_2M);
	}

	//secure loader address to system physical address
	//note: secure loader runs in a DS relative addressing mode
	//(relative to secure loader base address)
	static inline spa_t sla2spa(void *sla){
		return (spa_t) ((sla_t)sla + (rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M));
	}

	// XMHF runtime virtual-address to system-physical-address and vice-versa
	// Note: since we are unity mapped, runtime VA = system PA
	static inline spa_t hva2spa(void *hva){
		hva_t hva_ui = (hva_t)hva;
		return hva_ui;
	}

	static inline void * spa2hva(spa_t spa){
		return (void *)(hva_t)spa;
	}

	static inline spa_t gpa2spa(gpa_t gpa) { return gpa; }
	static inline gpa_t spa2gpa(spa_t spa) { return spa; }
	static inline void* gpa2hva(gpa_t gpa) { return spa2hva(gpa2spa(gpa)); }
	static inline gpa_t hva2gpa(void* hva) { return spa2gpa(hva2spa(hva)); }

#else //__XMHF_VERIFICATION__

	#define hva2spa(x) (u32)(x)
	static inline void * spa2hva(spa_t spa) { (void *)(hva_t)(spa); }
	static inline spa_t gpa2spa(gpa_t gpa) { return gpa; }
	static inline gpa_t spa2gpa(spa_t spa) { return spa; }
	static inline void* gpa2hva(gpa_t gpa) { return spa2hva(gpa2spa(gpa)); }
	static inline gpa_t hva2gpa(void* hva) { return spa2gpa(hva2spa(hva)); }

#endif //__XMHF_VERIFICATION__

#endif	//__ASSEMBLY__



#endif //__XMHF_BASEPLATFORM_H__
