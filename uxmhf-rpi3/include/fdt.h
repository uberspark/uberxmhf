/*
	flattened device tree blob definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __FDT_H__
#define __FDT_H__

#define FDT_MAGIC	0xedfe0dd0

#ifndef __ASSEMBLY__

// DT spec. v0.1

struct fdt_header {
	u32 magic;
	u32 totalsize;
	u32 off_dt_struct;
	u32 off_dt_strings;
	u32 off_mem_rsvmap;
	u32 version;
	u32 last_comp_version;
	u32 boot_cpuid_phys;
	u32 size_dt_strings;
	u32 size_dt_struct;
};

#endif // __ASSEMBLY__


#endif //__FDT_H__
