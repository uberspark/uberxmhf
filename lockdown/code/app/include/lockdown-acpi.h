// Advanced Configuration and Power-management Interface (ACPI) definitions
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __LOCKDOWN_ACPI_H__
#define __LOCKDOWN_ACPI_H__

#ifndef __ASSEMBLY__

extern u64 __PM1a_STS, __PM1a_EN, __PM1b_STS, __PM1b_EN;
extern u64 __PM1_CNTa, __PM1_CNTb;
extern u32 __PM1a_STS_size, __PM1a_EN_size, __PM1b_STS_size, __PM1b_EN_size;
extern u32 __PM1_CNTa_size, __PM1_CNTb_size;

#define PM1a_STS			__PM1a_STS
#define PM1a_STS_SIZE	__PM1a_STS_size
#define PM1a_EN				__PM1a_EN
#define PM1a_EN_SIZE	__PM1a_EN_size
#define PM1b_STS			__PM1b_STS
#define PM1b_STS_SIZE	__PM1b_STS_size
#define PM1b_EN				__PM1b_EN
#define PM1b_EN_SIZE	__PM1b_EN_size
#define PM1_CNTa			__PM1_CNTa
#define PM1_CNTa_SIZE	__PM1_CNTa_size
#define PM1_CNTb			__PM1_CNTb
#define PM1_CNTb_SIZE	__PM1_CNTb_size

void ACPIInitializeRegisters(void);

#endif //__ASSEMBLY__

#endif //__LOCKDOWN_ACPI_H__
