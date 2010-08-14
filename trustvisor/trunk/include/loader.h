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

/* loader.h - Loader specific definitions
 * Written for TrustVisor by Arvind Seshadri and Ning Qu
 */

#ifndef __LOADER_H_
#define __LOADER_H_

#define ENTRY(x)\
  .globl x;	\
  .align;	\
  x:
#define ALIGN .align 4, 0x00

#define __LOADER_CS 0x0008 	/* Selector for GDT entry 1. RPL 0 */
#define __LOADER_DS 0x0010 	/* Selector for GDT enry 0. RPL 0 */
/* SKIP TSS 0x0018 */
/* Selectors for real-mode AP descriptors */
#define __LOADER_CS16    0x0020
#define __LOADER_DS16    0x0028

#define LOADER_START 0x1800000 /* 24 MB */
#define LOADER_STACK_SIZE 0x1000 /* 4KB stack */

#define LOADER_REAL_START 0x20000

#define LINUX_BOOT_CS	0x1020
#define LINUX_BOOT_DS	0x1000
#define LINUX_BOOT_SP	0x9000

/* these two entries define the code, data and stack segment selectors 
 * for used to switch into real-mode. the corresponding segment 
 * descriptors define 16-bit segments. see loader code in boot/boot.S 
 * for the GDT.
 */
#define __ENTRY_CS 0x0018 	/* Selector for GDT entry 3. RPL 0 */
#define __ENTRY_DS 0x0020 	/* Selector for GDT enry 4. RPL 0 */

/* The TrustVisor Loader transfers control to the TrustVisor Init code
 * using AMD's SKINIT instruction.  This instruction requires
 * rendezvous of Application Processors.  Thus, we must initialize
 * them.
 */
#define NR_CPUS 8 /* Max number of CPUs */
#define MSR_K8_VM_CR                    0xC0010114

/* Synchronize this definition with the definition of VISOR_LOAD_START
 * in visor.h in TrustVisor's source tree.
 */
#define VISOR_START_ADDR 0x1E00000

#endif /* __LOADER_H_ */
