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

// memp-x86vmx-eptlock.c
// Control read and write access to EPT
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>

/*
 * When walking page table using software, race conditions between CPUs can
 * happen when when another CPU is modifying page table entries. For example:
 *
 * | CPU 0                              | CPU 1                               |
 * |------------------------------------|-------------------------------------|
 * | Get EPTP (from VMCS)               |                                     |
 * | Get PML4E (EPTP[offset])           |                                     |
 * | Get PDPTE (PML4E[offset])          |                                     |
 * | Get PDE (PDPTE[offset])            |                                     |
 * | Get PTE (PDE[offset])              |                                     |
 * |                                    | Quiesce all other CPUS              |
 * |                                    | Modify PTE, mark as not present     |
 * |                                    | Unquiesce all other CPUS            |
 * |                                    | Write sensitive data to page of PTE |
 * | Inspect PTE, looks present         |                                     |
 * | Access data (*(PTE.addr + offset)) |                                     |
 *
 * To fix this race condition, we use the idea of a read write lock. The
 * guidelines to synchronize are:
 * * When walking EPT with software, hold the read lock using
 *   memprot_x86vmx_eptlock_read_lock() and
 *   memprot_x86vmx_eptlock_read_unlock().
 * * When modifying EPT that affects other CPUs, hold the write lock using
 *   memprot_x86vmx_eptlock_write_lock() and
 *   memprot_x86vmx_eptlock_write_unlock().
 * * When quiescing, hold the write lock to prevent deadlocking.
 *
 * Lock design:
 *
 * Each CPU may only lock once at a time, so the number of threads is constant.
 * We want to impose minimum overhead on readers when there are no writers.
 *
 * Global variable g_eptlock_write_lock to make sure there are only 1 writer at
 * a time. The writer uses g_eptlock_write_pending to signal to readers to stop
 * reading, so the waiting time of a writer is bounded. Each reader uses
 * vcpu->vmx_eptlock_reading to let the writer know the reader is in critical
 * section.
 *
 * Critical section analysis:
 * * Mutual exclusion: writer sets g_eptlock_write_pending when locking. If
 *   reader is in critical section, then vcpu->vmx_eptlock_reading must be
 *   true. Writer will wait for reader to exit critical section.
 * * Progress: after writer sets g_eptlock_write_pending, no more readers will
 *   enter critical section. Then writer enters critical section and release
 *   lock.
 * * Bounded waiting: when there are too many writers, readers may starve.
 *   However this problem also exists if the writer quiesces the readers.
 */

/* Spin lock to make sure there are only 1 writer */
static volatile u32 g_eptlock_write_lock = 1;

/* Global flag to indicate a write is waiting / writing */
static volatile bool g_eptlock_write_pending = false;

/* Acquire writer lock (modify EPT entries) */
void memprot_x86vmx_eptlock_write_lock(VCPU *vcpu)
{
	(void)vcpu;
	spin_lock(&g_eptlock_write_lock);
	HALT_ON_ERRORCOND(!g_eptlock_write_pending);
	g_eptlock_write_pending = true;
	mb();
	for (u32 i = 0; i < g_midtable_numentries; i++) {
		VCPU *other_vcpu = (VCPU *)g_midtable[i].vcpu_vaddr_ptr;
		while (other_vcpu->vmx_eptlock_reading) {
			xmhf_cpu_relax();
		}
	}
	mb();
}

/* Release writer lock */
void memprot_x86vmx_eptlock_write_unlock(VCPU *vcpu)
{
	(void)vcpu;
	mb();
	HALT_ON_ERRORCOND(g_eptlock_write_pending);
	g_eptlock_write_pending = false;
	spin_unlock(&g_eptlock_write_lock);
}

/* Acquire reader lock (access EPT entries) */
void memprot_x86vmx_eptlock_read_lock(VCPU *vcpu)
{
	mb();
	HALT_ON_ERRORCOND(!vcpu->vmx_eptlock_reading);
	while (1) {
		while (g_eptlock_write_pending) {
			xmhf_cpu_relax();
		}
		mb();
		vcpu->vmx_eptlock_reading = true;
		mb();
		if (!g_eptlock_write_pending) {
			break;
		}
		mb();
		vcpu->vmx_eptlock_reading = false;
		mb();
	}
	mb();
}

/* Release reader lock */
void memprot_x86vmx_eptlock_read_unlock(VCPU *vcpu)
{
	mb();
	HALT_ON_ERRORCOND(vcpu->vmx_eptlock_reading);
	vcpu->vmx_eptlock_reading = false;
	mb();
}
