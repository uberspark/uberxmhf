/*
	ARM 8 32-bit (aarch32) architecture definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __ARM8_32_H__
#define __ARM8_32_H__

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


#endif // __ASSEMBLY__

#endif //__ARM8_32_H__
