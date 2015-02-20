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

#ifndef __XMHFHW_H__
#define __XMHFHW_H__


//////xmhfhw_cpu

#define MAX_LCP_PO_DATA_SIZE     64*1024  /* 64k */

#ifndef __ASSEMBLY__

typedef struct {
    mtrr_def_type_t	    mtrr_def_type;
    int	                num_var_mtrrs;
    mtrr_physbase_t     mtrr_physbases[MAX_VARIABLE_MTRRS];
    mtrr_physmask_t     mtrr_physmasks[MAX_VARIABLE_MTRRS];
} __attribute__((packed)) mtrr_state_t;


/*
 * OS/loader to MLE structure
 *   - private to tboot (so can be any format we need)
 */

typedef struct {
    uint32_t          version;           /* currently 2 */
    mtrr_state_t      saved_mtrr_state;  /* saved prior to changes for SINIT */
    //multiboot_info_t* mbi;               /* needs to be restored to ebx */
    void *mbi;
    uint32_t          saved_misc_enable_msr;  /* saved prior to SENTER */
                                         /* PO policy data */
    uint8_t           lcp_po_data[MAX_LCP_PO_DATA_SIZE];
} __attribute__ ((packed)) os_mle_data_t;


/*
 * TXT heap data format and field accessor fns
 */

/*
 * offset                 length                      field
 * ------                 ------                      -----
 *  0                      8                          bios_data_size
 *  8                      bios_data_size - 8      bios_data
 *
 *  bios_data_size      8                          os_mle_data_size
 *  bios_data_size +    os_mle_data_size - 8       os_mle_data
 *   8
 *
 *  bios_data_size +    8                          os_sinit_data_size
 *   os_mle_data_size
 *  bios_data_size +    os_sinit_data_size - 8     os_sinit_data
 *   os_mle_data_size +
 *   8
 *
 *  bios_data_size +    8                          sinit_mle_data_size
 *   os_mle_data_size +
 *   os_sinit_data_size
 *  bios_data_size +    sinit_mle_data_size - 8    sinit_mle_data
 *   os_mle_data_size +
 *   os_sinit_data_size +
 *   8
 */



void xmhfhw_cpu_cpuid(u32 op, u32 *eax, u32 *ebx, u32 *ecx, u32 *edx);
uint64_t rdtsc64(void);
u64 read_cr0(void);
void write_cr0(u64 val);
u64 read_cr3(void);
u64 read_rsp(void);
void write_cr3(u64 val);
u64 read_cr4(void);
void write_cr4(u64 val);
void skinit(unsigned long eax);
u32 read_segreg_cs(void);
u32 read_segreg_ds(void);
u32 read_segreg_es(void);
u32 read_segreg_fs(void);
u32 read_segreg_gs(void);
u32 read_segreg_ss(void);
u16 read_tr_sel(void);
void wbinvd(void);
uint32_t bsrl(uint32_t mask);
__CASMFNDEF__(xmhfhw_cpu_disable_intr) static void xmhfhw_cpu_disable_intr(void);
void enable_intr(void);
u64 xgetbv(u32 xcr_reg);
void xsetbv(u32 xcr_reg, u64 value);
void sysexitq(u64 rip, u64 rsp);
void spin_lock(volatile u32 *lock);
void spin_unlock(volatile u32 *lock);
u64 xmhf_baseplatform_arch_x86_getgdtbase(void);
u64 xmhf_baseplatform_arch_x86_getidtbase(void);
u64  xmhf_baseplatform_arch_x86_gettssbase(void);
int fls(int mask);
u32 get_cpu_vendor_or_die(void);
bool xmhf_baseplatform_arch_x86_cpuhasxsavefeature(void);
u32 xmhf_baseplatform_arch_x86_getcpuvendor(void);
u32 xmhf_baseplatform_arch_getcpuvendor(void);


uint64_t read_pub_config_reg(uint32_t reg);
void write_pub_config_reg(uint32_t reg, uint64_t val);
uint64_t read_priv_config_reg(uint32_t reg);
void write_priv_config_reg(uint32_t reg, uint64_t val);
bool txt_is_launched(void);


void set_all_mtrrs(bool enable);
bool set_mem_type(void *base, uint32_t size, uint32_t mem_type);
void print_mtrrs(const mtrr_state_t *saved_state);
void xmhfhw_cpu_x86_save_mtrrs(mtrr_state_t *saved_state);
bool validate_mtrrs(const mtrr_state_t *saved_state);
void xmhfhw_cpu_x86_restore_mtrrs(mtrr_state_t *saved_state);


txt_heap_t *get_txt_heap(void);
uint64_t get_bios_data_size(txt_heap_t *heap);
bios_data_t *get_bios_data_start(txt_heap_t *heap);
uint64_t get_os_mle_data_size(txt_heap_t *heap);
os_mle_data_t *get_os_mle_data_start(txt_heap_t *heap);
uint64_t get_os_sinit_data_size(txt_heap_t *heap);
os_sinit_data_t *get_os_sinit_data_start(txt_heap_t *heap);
uint64_t get_sinit_mle_data_size(txt_heap_t *heap);
sinit_mle_data_t *get_sinit_mle_data_start(txt_heap_t *heap);


#endif //__ASSEMBLY__


//////xmhfhw_cpu_msr

#ifndef __ASSEMBLY__

void rdmsr(u32 msr, u32 *eax, u32 *edx);
void wrmsr(u32 msr, u32 eax, u32 edx);
u64 rdmsr64(u32 msr);
void wrmsr64(u32 msr, u64 newval);

#endif //__ASSEMBLY__


/*
//////xmhfhw_cpu_msr

#ifndef __ASSEMBLY__


#endif //__ASSEMBLY__
*/


/*#include <_xmhfhw_cpu.h> --
    #include <_xmhfhw_cpu_msr.h>
    #include <_xmhfhw_cpu_paging.h>
    #include <_xmhfhw_cpu_txt.h>
    #include <_xmhfhw_cpu_vmx.h>
    #include <_xmhfhw_cpu_legio.h>
    #include <_xmhfhw_cpu_mem.h>


#include <_xmhfhw_legio_pci.h>
#include <_xmhfhw_legio_pit.h>
#include <_xmhfhw_legio_keyb.h>
#include <_xmhfhw_sysmem_bios.h>
*/

#ifndef __ASSEMBLY__

typedef struct {
    vtd_pml4te_t pml4t[PAE_MAXPTRS_PER_PML4T];
    vtd_pdpte_t pdpt[PAE_MAXPTRS_PER_PDPT];
    vtd_pdte_t pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
    vtd_pte_t pt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];
}__attribute__((packed)) vtd_slpgtbl_t;

typedef struct {
    u64 addr_vtd_pml4t;
    u64 addr_vtd_pdpt;
}__attribute__((packed)) vtd_slpgtbl_handle_t;

#endif //__ASSEMBLY__

/*
#include <_xmhfhw_mmio_vtd.h>
#include <_xmhfhw_mmio_lapic.h>
*/

#endif // __XMHFHW_H__
