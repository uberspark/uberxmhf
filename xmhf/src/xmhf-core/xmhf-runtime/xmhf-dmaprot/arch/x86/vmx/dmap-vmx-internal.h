#include <xmhf.h>

extern struct dmap_vmx_cap g_vtd_cap;

//vt-d register access function
extern void _vtd_reg(VTD_DRHD *dmardevice, u32 access, u32 reg, void *value);

// Return true if verification of VT-d capabilities succeed.
// Success means:
// (0) <out_cap> must be valid
// (1) Same AGAW, MGAW, and ND across VT-d units
// (2) supported MGAW to ensure our host address width is supported (32-bits)
// (3) AGAW must support 39-bits or 48-bits
// (4) Number of domains must not be unsupported
extern bool _vtd_verify_cap(VTD_DRHD* vtd_drhd, u32 vtd_num_drhd, struct dmap_vmx_cap* out_cap);

//initialize a DRHD unit
//note that the VT-d documentation does not describe the precise sequence of
//steps that need to be followed to initialize a DRHD unit!. we use our
//common sense instead...:p
extern void _vtd_drhd_initialize(VTD_DRHD *drhd, u32 vtd_ret_paddr);