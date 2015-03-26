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


CASM_FUNCDECL(void cpu_relax(void));
CASM_FUNCDECL(void xmhfhw_cpu_cpuid(u32 op, u32 *eax, u32 *ebx, u32 *ecx, u32 *edx));
CASM_FUNCDECL(uint64_t rdtsc64(void));
CASM_FUNCDECL(u32 read_eflags(void));
CASM_FUNCDECL(void write_eflags(u32 eflags));
CASM_FUNCDECL(u64 read_cr0(void));
CASM_FUNCDECL(void write_cr0(u64 val));
CASM_FUNCDECL(u32 read_cr2(void));
CASM_FUNCDECL(u64 read_cr3(void));
CASM_FUNCDECL(u64 read_rsp(void));
CASM_FUNCDECL(u32 read_esp(void));
CASM_FUNCDECL(void write_cr3(u64 val));
CASM_FUNCDECL(u64 read_cr4(void));
CASM_FUNCDECL(void write_cr4(u64 val));
//void skinit(unsigned long eax));
CASM_FUNCDECL(u32 read_segreg_cs(void));
CASM_FUNCDECL(u32 read_segreg_ds(void));
CASM_FUNCDECL(u32 read_segreg_es(void));
CASM_FUNCDECL(u32 read_segreg_fs(void));
CASM_FUNCDECL(u32 read_segreg_gs(void));
CASM_FUNCDECL(u32 read_segreg_ss(void));
CASM_FUNCDECL(u16 read_tr_sel(void));
CASM_FUNCDECL(void wbinvd(void));
CASM_FUNCDECL(uint32_t bsrl(uint32_t mask));
CASM_FUNCDECL(void xmhfhw_cpu_disable_intr(void));
CASM_FUNCDECL(void enable_intr(void));
CASM_FUNCDECL(u64 xgetbv(u32 xcr_reg));
CASM_FUNCDECL(void xsetbv(u32 xcr_reg, u64 value));
//void sysexitq(u64 rip, u64 rsp));
CASM_FUNCDECL(void spin_lock(volatile u32 *lock));
CASM_FUNCDECL(void spin_unlock(volatile u32 *lock));
CASM_FUNCDECL(void xmhfhw_cpu_loadGDT(arch_x86_gdtdesc_t *gdt_addr));
CASM_FUNCDECL(void xmhfhw_cpu_loadTR(u32 tr_selector));
CASM_FUNCDECL(void xmhfhw_cpu_loadIDT(arch_x86_idtdesc_t *idt_addr));
CASM_FUNCDECL(u64 xmhf_baseplatform_arch_x86_getgdtbase(void));
CASM_FUNCDECL(u64 xmhf_baseplatform_arch_x86_getidtbase(void));
CASM_FUNCDECL(u64  xmhf_baseplatform_arch_x86_gettssbase(void));


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
bool set_mem_type(u8 *base, uint32_t size, uint32_t mem_type);
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
CASM_FUNCDECL(u64 rdmsr64(u32 msr));
CASM_FUNCDECL(void wrmsr64(u32 msr, u64 newval));

#endif //__ASSEMBLY__



//////xmhfhw_cpu_paging


#ifndef __ASSEMBLY__

CASM_FUNCDECL(void cache_wbinvd(void));
CASM_FUNCDECL(void tlb_invlpg(u64 addr));

#endif //__ASSEMBLY__



//////xmhfhw_cpu_txt

#ifndef __ASSEMBLY__

CASM_FUNCDECL(void xmhfhw_cpu_getsec(u32 *eax, u32 *ebx, u32 *ecx, u32 *edx));
CASM_FUNCDECL(uint64_t read_config_reg(uint32_t config_regs_base, uint32_t reg));
CASM_FUNCDECL(void write_config_reg(uint32_t config_regs_base, uint32_t reg, uint64_t val));
uint32_t __getsec_capabilities(uint32_t index);
void __getsec_senter(uint32_t sinit_base, uint32_t sinit_size);
void __getsec_sexit(void);
void __getsec_wakeup(void);
void __getsec_smctrl(void);
void __getsec_parameters(uint32_t index, int* param_type, uint32_t* peax, uint32_t* pebx, uint32_t* pecx);


#endif //__ASSEMBLY__


//////xmhfhw_cpu_vmx

#ifndef __ASSEMBLY__

CASM_FUNCDECL(bool __vmx_vmxon(u64 vmxonregion_paddr));
CASM_FUNCDECL(void xmhfhw_cpu_x86vmx_vmwrite(u32 encoding, u32 value));
CASM_FUNCDECL(u32 xmhfhw_cpu_x86vmx_vmread(u32 encoding));
CASM_FUNCDECL(u32 __vmx_vmclear(u64 vmcs));
CASM_FUNCDECL(u32 __vmx_vmptrld(u64 vmcs));
CASM_FUNCDECL(u32 __vmx_invvpid(int invalidation_type, u32 vpid, u32 linearaddress));
CASM_FUNCDECL(void __vmx_invept(u64 invalidation_type, u64 eptp));

#endif //__ASSEMBLY__



//////xmhfhw_cpu_legio

#ifndef __ASSEMBLY__

CASM_FUNCDECL(void outl(u32 val, u32 port));
CASM_FUNCDECL(void outw (u32 value, u32 port));
CASM_FUNCDECL(void outb (u32 value, u32 port));
CASM_FUNCDECL(u32 inl(u32 port));
CASM_FUNCDECL(u16 inw (u32 port));
CASM_FUNCDECL(u8 inb (u32 port));

#endif //__ASSEMBLY__





//////xmhfhw_cpu_mem

#ifndef __ASSEMBLY__

void * hva2sla(void *hva);
spa_t sla2spa(void *sla);
spa_t hva2spa(void *hva);
void * spa2hva(spa_t spa);
spa_t gpa2spa(gpa_t gpa);
gpa_t spa2gpa(spa_t spa);
void* gpa2hva(gpa_t gpa);
gpa_t hva2gpa(hva_t hva);
u8 xmhfhw_sysmemaccess_readu8(u32 addr);
u16 xmhfhw_sysmemaccess_readu16(u32 addr);
u32 xmhfhw_sysmemaccess_readu32(u32 addr);
u64 xmhfhw_sysmemaccess_readu64(u32 addr);
void xmhfhw_sysmemaccess_writeu8(u32 addr, u8 val);
void xmhfhw_sysmemaccess_writeu16(u32 addr, u16 val);
void xmhfhw_sysmemaccess_writeu32(u32 addr, u32 val);
void xmhfhw_sysmemaccess_writeu64(u32 addr, u64 val);
void xmhfhw_sysmemaccess_copy(u8 *dest, u8 *src, u32 size);

#endif //__ASSEMBLY__



//////xmhfhw_legio_pci

#ifndef __ASSEMBLY__

void xmhf_baseplatform_arch_x86_pci_type1_read(u32 bus, u32 device, u32 function, u32 index, u32 len, u32 *value);
void xmhf_baseplatform_arch_x86_pci_type1_write(u32 bus, u32 device, u32 function, u32 index, u32 len, u32 value);
void xmhfhw_platform_bus_init(void);

#endif //__ASSEMBLY__



//////xmhfhw_legio_pit

#ifndef __ASSEMBLY__

void xmhf_baseplatform_arch_x86_udelay(u32 usecs);

#endif //__ASSEMBLY__



//////xmhfhw_legio_keyb

#ifndef __ASSEMBLY__

void xmhf_baseplatform_arch_x86_reboot(void);

#endif //__ASSEMBLY__


//////xmhfhw_sysmem_bios

#ifndef __ASSEMBLY__

u32 xmhfhw_platform_x86pc_acpi_getRSDP(ACPI_RSDP *rsdp);

#endif //__ASSEMBLY__


//////xmhfhw_mmio_vtd

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

//vt-d register access function
u64 _vtd_reg_read(VTD_DRHD *dmardevice, u32 reg);
void _vtd_reg_write(VTD_DRHD *dmardevice, u32 reg, u64 value);
VTD_DRHD *_vtd_get_drhd_struct(vtd_drhd_handle_t drhd_handle);
bool xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(vtd_drhd_handle_t *maxhandle, u32 *dmar_phys_addr_var);
bool xmhfhw_platform_x86pc_vtd_drhd_initialize(vtd_drhd_handle_t drhd_handle);
bool xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(vtd_drhd_handle_t drhd_handle);
bool xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(vtd_drhd_handle_t drhd_handle,  u64 ret_addr);
void xmhfhw_platform_x86pc_vtd_drhd_enable_translation(vtd_drhd_handle_t drhd_handle);
void xmhfhw_platform_x86pc_vtd_drhd_disable_translation(vtd_drhd_handle_t drhd_handle);
void xmhfhw_platform_x86pc_vtd_drhd_enable_pmr(vtd_drhd_handle_t drhd_handle);
void xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(vtd_drhd_handle_t drhd_handle);
void xmhfhw_platform_x86pc_vtd_drhd_set_plm_base_and_limit(vtd_drhd_handle_t drhd_handle, u32 base, u32 limit);
void xmhfhw_platform_x86pc_vtd_drhd_set_phm_base_and_limit(vtd_drhd_handle_t drhd_handle, u64 base, u64 limit);
u64 xmhfhw_platform_x86pc_vtd_drhd_reg_read(vtd_drhd_handle_t drhd_handle, u32 reg);
void xmhfhw_platform_x86pc_vtd_drhd_reg_write(vtd_drhd_handle_t drhd_handle, u32 reg, u64 value);


#endif //__ASSEMBLY__


//////xmhfhw_mmio_lapic

#ifndef __ASSEMBLY__

u32 xmhf_baseplatform_arch_x86_getcpulapicid(void);

#endif //__ASSEMBLY__



#endif // __XMHFHW_H__
