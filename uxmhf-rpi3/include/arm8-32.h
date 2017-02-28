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
#define LDESC_S2_MEMATTR_MA_MASK	0x000000000000003CULL
#define LDESC_S2_MEMATTR_MA_SHIFT	2



/*
LDESC_MAKE_S2_L1E_xxx

L1E_INVALID
L1E_TABLE

L2E_INVALID
L2E_TABLE

L3E_PAGE
L3E_INVALID
L3E_RESINVALID
*/



#ifndef __ASSEMBLY__

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

#endif // __ASSEMBLY__

#endif //__ARM8_32_H__
