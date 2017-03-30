/*
	ARM 8 32-bit (aarch32) architecture definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __ARM8_32_H__
#define __ARM8_32_H__

//
// memory shareability types
//
#define	MEM_NON_SHAREABLE		0x0
#define MEM_OUTER_SHAREABLE		0x2
#define	MEM_INNER_SHAREABLE		0x3

//
// memory cacheability types
//
#define	MEM_NON_CACHEABLE								0x0
#define MEM_WRITEBACK_READALLOCATE_WRITEALLOCATE		0x1
#define	MEM_WRITETHROUGH_READALLOCATE_NOWRITEALLOCATE	0x2
#define MEM_WRITEBACK_READALLOCATE_NOWRITEALLOCATE		0x3


//
// VTCR (virtualization translation control register) bit definitions
// G6.2.161 ARMv8
//
#define VTCR_RES1_MASK		0x80000000
#define	VTCR_SH0_MASK		0x00003000
#define VTCR_SH0_SHIFT		12
#define	VTCR_ORGN0_MASK		0x00000C00
#define VTCR_ORGN0_SHIFT	10
#define	VTCR_IRGN0_MASK		0x00000300
#define VTCR_IRGN0_SHIFT	8
#define	VTCR_SL0_MASK		0x000000C0
#define VTCR_SL0_SHIFT		6
#define	VTCR_S_MASK			0x00000010
#define	VTCR_S_SHIFT		4
#define	VTCR_T0SZ_MASK		0x0000000F
#define	VTCR_T0SZ_SHIFT		0

//
// HDCR (hyp debug control register) bit definitions
// 4.5.38 Cortex-A53 TRM
//
#define HDCR_TDRA_MASK		0x00000800
#define HDCR_TDRA_SHIFT		11
#define HDCR_TDOSA_MASK		0x00000400
#define HDCR_TDOSA_SHIFT	10
#define HDCR_TDA_MASK		0x00000200
#define HDCR_TDA_SHIFT		9
#define HDCR_TDE_MASK		0x00000100
#define HDCR_TDE_SHIFT		8
#define HDCR_HPME_MASK		0x00000080
#define HDCR_HPME_SHIFT		7
#define HDCR_TPM_MASK		0x00000060
#define HDCR_TPM_SHIFT		6
#define HDCR_TPMCR_MASK		0x00000020
#define HDCR_TPMCR_SHIFT	5
#define HDCR_HPMN_MASK		0x0000001f
#define HDCR_HPMN_SHIFT		0


//
// HCPTR (hyp architectural feature trap register) bit definitions
// G6.2.57 ARMv8
//
#define HCPTR_RES1_MASK		0x000033ff
#define HCPTR_TTA_MASK		0x00100000
#define HCPTR_TTA_SHIFT		20
#define HCPTR_TASE_MASK		0x00008000
#define HCPTR_TASE_SHIFT	15
#define HCPTR_TCP11_MASK	0x00000800
#define HCPTR_TCP11_SHIFT	11
#define HCPTR_TCP10_MASK	0x00000600
#define HCPTR_TCP10_SHIFT	10


//
// stage-2 long descriptor memory attribute bit definitions for
// BLOCK and PAGE descriptors
// G4.5.3 ARMv8
//
#define LDESC_S2_MEMATTR_XN_MASK	0x0040000000000000ULL
#define LDESC_S2_MEMATTR_XN_SHIFT	54
#define LDESC_S2_MEMATTR_C_MASK		0x0010000000000000ULL
#define LDESC_S2_MEMATTR_C_SHIFT	52
#define LDESC_S2_MEMATTR_AF_MASK	0x0000000000000400ULL
#define LDESC_S2_MEMATTR_AF_SHIFT	10
#define LDESC_S2_MEMATTR_SH_MASK	0x0000000000000300ULL
#define LDESC_S2_MEMATTR_SH_SHIFT	8
#define LDESC_S2_MEMATTR_S2AP_MASK	0x00000000000000C0ULL
#define LDESC_S2_MEMATTR_S2AP_SHIFT	6
#define LDESC_S2_MEMATTR_MC_MASK	0x000000000000003CULL
#define LDESC_S2_MEMATTR_MC_SHIFT	2


//
// stage-2 long descriptor memory access permission definitions for
// BLOCK and PAGE descriptors
// G4.6.5 ARMv8
//
#define LDESC_S2_S2AP_NO_ACCESS		0x0
#define LDESC_S2_S2AP_READ_ONLY		0x1
#define LDESC_S2_S2AP_WRITE_ONLY	0x2
#define LDESC_S2_S2AP_READ_WRITE	0x3


//
// stage-2 long descriptor memory cacheability definitions for
// BLOCK and PAGE descriptors
// G4.7.5 ARMv8
//
#define LDESC_S2_MC_DEVnGnRnE														0x0
#define LDESC_S2_MC_DEVnGnRE														0x1
#define LDESC_S2_MC_DEVnGRE															0x2
#define LDESC_S2_MC_DEVGRE															0x3
#define LDESC_S2_MC_OUTER_NON_CACHEABLE_RESERVED 									0x4
#define LDESC_S2_MC_OUTER_NON_CACHEABLE_INNER_NON_CACHEABLE 						0x5
#define LDESC_S2_MC_OUTER_NON_CACHEABLE_INNER_WRITE_THROUGH_CACHEABLE 				0x6
#define LDESC_S2_MC_OUTER_NON_CACHEABLE_INNER_WRITE_BACK_CACHEABLE 					0x7
#define LDESC_S2_MC_OUTER_WRITE_THROUGH_CACHEABLE_RESERVED 							0x8
#define LDESC_S2_MC_OUTER_WRITE_THROUGH_CACHEABLE_INNER_NON_CACHEABLE 				0x9
#define LDESC_S2_MC_OUTER_WRITE_THROUGH_CACHEABLE_INNER_WRITE_THROUGH_CACHEABLE 	0xa
#define LDESC_S2_MC_OUTER_WRITE_THROUGH_CACHEABLE_INNER_WRITE_BACK_CACHEABLE 		0xb
#define LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_RESERVED 							0xc
#define LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_NON_CACHEABLE 					0xd
#define LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_THROUGH_CACHEABLE 		0xe
#define LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_BACK_CACHEABLE 			0xf


//
// stage-2 long descriptor translation table format descriptor macros
// G4.5.2 ARMv8
//
#define ldesc_make_s2_l1e_invalid()	0x0ULL

#define ldesc_make_s2_l1e_table(addr)	\
		((addr & 0x000000FFFFFFF000ULL) | 0x3ULL)

#define ldesc_make_s2_l1e_block(addr, attrs)	\
		((addr & 0x000000FFC0000000ULL) | attrs | 0x1ULL)

#define ldesc_make_s2_l2e_invalid()	0x0ULL

#define ldesc_make_s2_l2e_block(addr, attrs)	\
		((addr & 0x000000FFFFE00000ULL) | attrs | 0x1ULL)

#define ldesc_make_s2_l2e_table(addr)	\
		((addr & 0x000000FFFFFFF000ULL) | 0x3ULL)

#define ldesc_make_s2_l3e_invalid()	0x0ULL

#define ldesc_make_s2_l3e_resinvalid()	0x1ULL

#define ldesc_make_s2_l3e_page(addr, attrs)	\
		((addr & 0x000000FFFFFFF000ULL) | attrs | 0x3ULL)


#define L1_LDESC_TABLE_MAXENTRIES	1024
#define L1_LDESC_TABLE_ENTRIES		3
#define L2_LDESC_TABLE_MAXENTRIES	512
#define L3_LDESC_TABLE_MAXENTRIES	512

#define PAGE_SIZE_4K					4096
#define PAGE_SIZE_2M					0x00200000UL
#define PAGE_SIZE_1G					0x40000000UL

//
// VTTBR (virtualization translation table base register) bit definitions
// G6.2.162 ARMv8
//
#define VTTBR_VMID_MASK				0x00FF000000000000ULL
#define VTTBR_VMID_SHIFT			48
#define VTTBR_BADDR_MASK			0x0000FFFFFFFFFFFFULL
#define VTTBR_BADDR_SHIFT			0


//
// HCR (hyp configuration register) bit definitions
// G6.2.58 ARMv8
//
#define HCR_VM_MASK					0x00000001UL
#define HCR_VM_SHIFT				0


//
// HSR (hyp syndrome register) bit definitions
// G6.2.67 ARMv8
//
#define HSR_EC_MASK			0xFC000000UL
#define HSR_EC_SHIFT		26
#define HSR_IL_MASK			0x02000000UL
#define HSR_IL_SHIFT		25
#define HSR_ISS_MASK		0x1FFFFFFFUL
#define HSR_ISS_SHIFT		0

//
// HSR (hyp syndrome register) EC values
// G6.2.67 ARMv8
//
#define HSR_EC_HVC							0x12
#define HSR_EC_PREFETCH_ABORT_ELCHANGE		0x20
#define HSR_EC_PREFETCH_ABORT_NOELCHANGE	0x21
#define HSR_EC_DATA_ABORT_ELCHANGE			0x24
#define HSR_EC_DATA_ABORT_NOELCHANGE		0x25



#ifndef __ASSEMBLY__


static inline u32 cpu_bswap_u32(u32 val){
    val = ((val << 8) & 0xFF00FF00 ) | ((val >> 8) & 0xFF00FF );
    return (val << 16) | (val >> 16);
}

static inline u64 cpu_bswap_u64(u64 val){
	val = ((val << 8) & 0xFF00FF00FF00FF00ULL ) | ((val >> 8) & 0x00FF00FF00FF00FFULL );
    val = ((val << 16) & 0xFFFF0000FFFF0000ULL ) | ((val >> 16) & 0x0000FFFF0000FFFFULL );
    return (val << 32) | (val >> 32);
}


#define cpu_be2le_u32(be_val_u32)	cpu_bswap_u32(be_val_u32)
#define cpu_be2le_u64(be_val_u64)	cpu_bswap_u64(be_val_u64)
#define cpu_le2be_u32(le_val_u32)	cpu_bswap_u32(le_val_u32)
#define cpu_le2be_u64(le_val_u64)	cpu_bswap_u64(le_val_u64)



extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);

extern u32 sysreg_read_scr(void);

extern u32 sysreg_read_cpsr(void);

extern u32 sysreg_read_hvbar(void);
extern void sysreg_write_hvbar(u32 value);

extern u32 sysreg_read_hcr(void);
extern void sysreg_write_hcr(u32 value);

extern u32 sysreg_read_spsr_hyp(void);

extern u32 sysreg_read_hsctlr(void);
extern void sysreg_write_hsctlr(u32 value);

extern void hypcall(void);

extern void svccall(void);

extern u32 sysreg_read_sctlr(void);
extern void sysreg_write_sctlr(u32 value);


extern u32 sysreg_read_vbar(void);
extern void sysreg_write_vbar(u32 value);

extern u32 sysreg_read_vtcr(void);
extern void sysreg_write_vtcr(u32 value);

extern u32 sysreg_read_hdcr(void);
extern void sysreg_write_hdcr(u32 value);

extern u32 sysreg_read_hcptr(void);
extern void sysreg_write_hcptr(u32 value);

extern u32 sysreg_read_hstr(void);
extern void sysreg_write_hstr(u32 value);

extern u64 sysreg_read_vttbr(void);
extern void sysreg_write_vttbr(u64 value);

extern u32 sysreg_read_hsr(void);

extern u32 sysreg_read_elrhyp(void);
extern void sysreg_write_elrhyp(u32 value);

extern void sysreg_tlbiallh(void);


void spin_lock(u32 *lock);



#endif // __ASSEMBLY__

#endif //__ARM8_32_H__
