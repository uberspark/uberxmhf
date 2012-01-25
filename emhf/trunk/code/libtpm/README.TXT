libtpm needs some environment specific functions to be 
defined by the target environment using it. The following
are the required functions:

void cpu_relax(void);
void _read_tpm_reg(int locality, u32 reg, u8 *_raw, size_t size);
void _write_tpm_reg(int locality, u32 reg, u8 *_raw, size_t size);

for EMHF, these are defined in the emhf-tpm component; more
specifically in emhf-tpm/arch/x86/tpm-x86.c

