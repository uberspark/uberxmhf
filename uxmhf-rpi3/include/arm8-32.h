/*
	ARM 8 32-bit (aarch32) architecture definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __ARM8_32_H__
#define __ARM8_32_H__



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


#endif // __ASSEMBLY__

#endif //__ARM8_32_H__
