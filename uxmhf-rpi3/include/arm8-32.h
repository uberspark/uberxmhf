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


#endif // __ASSEMBLY__

#endif //__ARM8_32_H__
