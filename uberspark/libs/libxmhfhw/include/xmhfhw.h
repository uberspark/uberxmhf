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

//#define MAX_LCP_PO_DATA_SIZE     64*1024  /* 64k */
#define MAX_LCP_PO_DATA_SIZE     64

#ifndef __ASSEMBLY__

typedef struct {
    mtrr_def_type_t	    mtrr_def_type;
    u32	                num_var_mtrrs;
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

#endif //__ASSEMBLY__





/*@
  assigns \nothing;
@*/
int fls(int mask);

/*@
  assigns \nothing;
@*/
uint32_t __getsec_capabilities(uint32_t index);

/*@
	requires \valid(param_type);
	requires \valid(peax);
	requires \valid(pebx);
	requires \valid(pecx);
	assigns *param_type;
	assigns *peax;
	assigns *pebx;
	assigns *pecx;
@*/
void __getsec_parameters(uint32_t index, int* param_type, uint32_t* peax, uint32_t* pebx, uint32_t* pecx);


/*@
  assigns \nothing;
@*/
void __getsec_senter(uint32_t sinit_base, uint32_t sinit_size);

/*@
  assigns \nothing;
@*/
void __getsec_sexit(void);

/*@
  assigns \nothing;
@*/
void __getsec_smctrl(void);

/*@
  assigns \nothing;
@*/
void __getsec_wakeup(void);


/*@
  assigns \nothing;
@*/
u32 xmhf_baseplatform_arch_getcpuvendor(void);


/*@
  assigns \nothing;
@*/
bool xmhf_baseplatform_arch_x86_cpuhasxsavefeature(void);

/*@
  assigns \nothing;
@*/
void set_all_mtrrs(bool enable);


/*@
	requires \valid(saved_state);
	requires 0 <= saved_state->num_var_mtrrs < MAX_VARIABLE_MTRRS;
	assigns \nothing;
@*/
void xmhfhw_cpu_x86_restore_mtrrs(mtrr_state_t *saved_state);


/*@
	requires \valid(saved_state);
	assigns saved_state->mtrr_def_type;
	assigns saved_state->num_var_mtrrs;
	assigns saved_state->mtrr_physbases[0 .. MAX_VARIABLE_MTRRS-1];
	assigns saved_state->mtrr_physmasks[0 .. MAX_VARIABLE_MTRRS-1];
@*/
void xmhfhw_cpu_x86_save_mtrrs(mtrr_state_t *saved_state);


bool set_mem_type(u32 base, uint32_t size, uint32_t mem_type);

/*@
	requires \valid(saved_state);
	requires 0 <= saved_state->num_var_mtrrs < MAX_VARIABLE_MTRRS;
	assigns \nothing;
@*/
bool validate_mtrrs(mtrr_state_t *saved_state);





/*@
	assigns \nothing;
@*/
uint64_t get_bios_data_size(u32 heap_memaddr, uint32_t heap_size);


/*@
	assigns \nothing;
@*/
u32 get_bios_data_start(u32 heap_memaddr, uint32_t heap_size);



/*@
	assigns \nothing;
@*/
u32 get_txt_heap(void);


/*@
	assigns \nothing;
@*/
uint64_t get_os_mle_data_size(u32 heap_memaddr, uint32_t heap_size);


/*@
	assigns \nothing;
@*/
u32 get_os_mle_data_start(u32 heap_memaddr, uint32_t heap_size);

/*@
	assigns \nothing;
@*/
uint64_t get_os_sinit_data_size(u32 heap_memaddr, uint32_t heap_size);

/*@
	assigns \nothing;
@*/
u32 get_os_sinit_data_start(u32 heap_memaddr, uint32_t heap_size);

/*@
	assigns \nothing;
@*/
uint64_t get_sinit_mle_data_size(u32 heap_memaddr, uint32_t heap_size);

/*@
	assigns \nothing;
@*/
u32 get_sinit_mle_data_start(u32 heap_memaddr, uint32_t heap_size);

/*@
	assigns \nothing;
@*/
bool txt_is_launched(void);

/*@
	assigns \nothing;
@*/
uint64_t read_priv_config_reg(uint32_t reg);


/*@
	assigns \nothing;
@*/
uint64_t read_pub_config_reg(uint32_t reg);

/*@
	assigns \nothing;
@*/
void write_priv_config_reg(uint32_t reg, uint64_t val);

/*@
	assigns \nothing;
@*/
void write_pub_config_reg(uint32_t reg, uint64_t val);




/*@
	assigns \nothing;
@*/
void xmhf_baseplatform_arch_x86_reboot(void);



/*@
	assigns \nothing;
@*/
u32 xmhf_baseplatform_arch_x86_getcpulapicid(void);


/*@
	assigns \nothing;
@*/
bool xmhfhw_lapic_isbsp(void);



/*@
	assigns \nothing;
@*/
bool xmhfhw_platform_bus_init(void);


/*@
	requires \valid(value);
	assigns *value;
	ensures 0 <= (*value) <= 0xFFFFFFFFUL;
@*/
void xmhf_baseplatform_arch_x86_pci_type1_read(u32 bus, u32 device, u32 function, u32 index, u32 len, u32 *value);

/*@
	assigns \nothing;
@*/
void xmhf_baseplatform_arch_x86_pci_type1_write(u32 bus, u32 device, u32 function, u32 index, u32 len, u32 value);


/*@
	assigns \nothing;
@*/
void xmhf_baseplatform_arch_x86_udelay(u32 usecs);


/*@
	requires \valid(rsdp);
	assigns \nothing;
@*/
u32 xmhfhw_platform_x86pc_acpi_getRSDP(ACPI_RSDP *rsdp);


/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
void xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(VTD_DRHD *drhd);

/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
void xmhfhw_platform_x86pc_vtd_drhd_disable_translation(VTD_DRHD *drhd);

/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
void xmhfhw_platform_x86pc_vtd_drhd_enable_translation(VTD_DRHD *drhd);

/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
bool xmhfhw_platform_x86pc_vtd_drhd_initialize(VTD_DRHD *drhd);

/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
bool xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(VTD_DRHD *drhd);

/*@
	requires \valid(dmardevice);
	assigns \nothing;
@*/
u64 _vtd_reg_read(VTD_DRHD *dmardevice, u32 reg);

/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
void xmhfhw_platform_x86pc_vtd_drhd_set_phm_base_and_limit(VTD_DRHD *drhd, u64 base, u64 limit);

/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
void xmhfhw_platform_x86pc_vtd_drhd_set_plm_base_and_limit(VTD_DRHD *drhd, u32 base, u32 limit);

/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
bool xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(VTD_DRHD *drhd,  u64 ret_addr);

/*@
	requires \valid(dmardevice);
	assigns \nothing;
@*/
void _vtd_reg_write(VTD_DRHD *dmardevice, u32 reg, u64 value);








/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(uint32_t bsrl(uint32_t mask));


/*@
	requires \valid(eax);
	requires \valid(ebx);
	requires \valid(ecx);
	requires \valid(edx);
	assigns *eax;
	assigns *ebx;
	assigns *ecx;
	assigns *edx;
@*/
CASM_FUNCDECL(void xmhfhw_cpu_getsec(u32 *eax, u32 *ebx, u32 *ecx, u32 *edx));


/*@
	requires \valid(eax);
	requires \valid(ebx);
	requires \valid(ecx);
	requires \valid(edx);
	assigns *eax;
	assigns *ebx;
	assigns *ecx;
	assigns *edx;
@*/
CASM_FUNCDECL(void xmhfhw_cpu_cpuid(u32 op, u32 *eax, u32 *ebx, u32 *ecx, u32 *edx));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void wrmsr64(u32 msr, u32 newval_lo, u32 newval_hi));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(u64 rdmsr64(u32 msr));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(u8 xmhfhw_sysmemaccess_readu8(u32 addr));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(u16 xmhfhw_sysmemaccess_readu16(u32 addr));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(u32 xmhfhw_sysmemaccess_readu32(u32 addr));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(u64 xmhfhw_sysmemaccess_readu64(u32 addr));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void xmhfhw_sysmemaccess_writeu8(u32 addr, u8 val));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void xmhfhw_sysmemaccess_writeu16(u32 addr, u16 val));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void xmhfhw_sysmemaccess_writeu32(u32 addr, u32 val));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void xmhfhw_sysmemaccess_writeu64(u32 addr, u32 val_lo, u32 val_hi));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void xmhfhw_sysmemaccess_copy(u8 *dest, u8 *src, u32 size));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void xmhfhw_sysmem_copy_sys2obj(u8 *objdst, u8 *syssrc, u32 size));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void xmhfhw_sysmem_copy_obj2sys(u8 *sysdst, u8 *objsrc, u32 size));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(uint64_t read_config_reg(uint32_t config_regs_base, uint32_t reg));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void write_config_reg(uint32_t config_regs_base, uint32_t reg, uint64_t val));




/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void outl(u32 val, u32 port));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void outw (u32 value, u32 port));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void outb (u32 value, u32 port));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(u32 inl(u32 port));

/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(u16 inw (u32 port));

/*@
  assigns \nothing;
  ensures 0 <= \result <= 255;
@*/
CASM_FUNCDECL(u8 inb (u32 port));





CASM_FUNCDECL(void xmhfhw_cpu_disable_intr(void *noparam));
CASM_FUNCDECL(void enable_intr(void *noparam));
CASM_FUNCDECL(u32 xmhf_baseplatform_arch_x86_getgdtbase(void *noparam));
CASM_FUNCDECL(u32 xmhf_baseplatform_arch_x86_getidtbase(void *noparam));
CASM_FUNCDECL(u64  xmhf_baseplatform_arch_x86_gettssbase(void *noparam));


/*@
  assigns \nothing;
@*/
CASM_FUNCDECL(void xmhfhw_cpu_hlt(void *noparam));



CASM_FUNCDECL(void cpu_relax(void *noparam));


CASM_FUNCDECL(uint64_t rdtsc64(void *noparam));
CASM_FUNCDECL(u32 read_eflags(void *noparam));

CASM_FUNCDECL(void write_eflags(u32 eflags));

CASM_FUNCDECL(u64 read_cr0(void *noparam));

CASM_FUNCDECL(void write_cr0(u32 val));

CASM_FUNCDECL(u32 read_cr2(void *noparam));
CASM_FUNCDECL(u64 read_cr3(void *noparam));
CASM_FUNCDECL(u64 read_rsp(void *noparam));
CASM_FUNCDECL(u32 read_esp(void *noparam));

CASM_FUNCDECL(void write_cr3(u32 val));

CASM_FUNCDECL(u64 read_cr4(void *noparam));

CASM_FUNCDECL(void write_cr4(u32 val));
//void skinit(unsigned long eax));

CASM_FUNCDECL(u32 read_segreg_cs(void *noparam));
CASM_FUNCDECL(u32 read_segreg_ds(void *noparam));
CASM_FUNCDECL(u32 read_segreg_es(void *noparam));
CASM_FUNCDECL(u32 read_segreg_fs(void *noparam));
CASM_FUNCDECL(u32 read_segreg_gs(void *noparam));
CASM_FUNCDECL(u32 read_segreg_ss(void *noparam));
CASM_FUNCDECL(u32 read_tr_sel(void *noparam));

CASM_FUNCDECL(void wbinvd(void *noparam));



CASM_FUNCDECL(u64 xgetbv(u32 xcr_reg));
CASM_FUNCDECL(void xsetbv(u32 xcr_reg, u32 value_lo, u32 value_hi));
//void sysexitq(u64 rip, u64 rsp));

/*@
  requires \valid(lock);
  assigns *lock;
@*/
CASM_FUNCDECL(void spin_lock(volatile u32 *lock));

/*@
  requires \valid(lock);
  assigns *lock;
@*/
CASM_FUNCDECL(void spin_unlock(volatile u32 *lock));

CASM_FUNCDECL(void xmhfhw_cpu_loadGDT(arch_x86_gdtdesc_t *gdt_addr));
CASM_FUNCDECL(void xmhfhw_cpu_loadTR(u32 tr_selector));
CASM_FUNCDECL(void xmhfhw_cpu_loadIDT(arch_x86_idtdesc_t *idt_addr));



u32 xmhf_baseplatform_arch_getcpuvendor(void);


CASM_FUNCDECL(void xmhfhw_cpu_reloadcs(u32 cs_sel));
CASM_FUNCDECL(void xmhfhw_cpu_reloaddsregs(u32 ds_sel));





#endif //__ASSEMBLY__



//////xmhfhw_cpu_paging


#ifndef __ASSEMBLY__

CASM_FUNCDECL(void cache_wbinvd(void *noparam));
CASM_FUNCDECL(void tlb_invlpg(u64 addr));

#endif //__ASSEMBLY__





//////xmhfhw_cpu_vmx

#ifndef __ASSEMBLY__

CASM_FUNCDECL(bool __vmx_vmxon(u64 vmxonregion_paddr));
CASM_FUNCDECL(void xmhfhw_cpu_x86vmx_vmwrite(u32 encoding, u32 value));
CASM_FUNCDECL(u32 xmhfhw_cpu_x86vmx_vmread(u32 encoding));
CASM_FUNCDECL(u32 __vmx_vmclear(u64 vmcs));
CASM_FUNCDECL(u32 __vmx_vmptrld(u64 vmcs));


CASM_FUNCDECL(void xmhfhw_cpu_invvpid(u32 invalidation_type, u32 vpid, u32 linear_addr_lo, u32 linear_addr_hi));

/*@
	assigns \nothing;
@*/
CASM_FUNCDECL(u32 __vmx_invept(u32 invalidation_type_lo, u32 invalidation_type_hi, u32 eptp_lo, u32 eptp_hi));

#endif //__ASSEMBLY__


















#endif // __XMHFHW_H__
