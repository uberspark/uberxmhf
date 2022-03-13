// author: Miao Yu [Superymk]
#ifndef XMHF_DMAP
#define XMHF_DMAP

#include <xmhf.h>

#ifndef __ASSEMBLY__

/// IOMMU PageTable information structure
typedef struct 
{
	iommu_pt_t			iommu_pt_id;
	IOMMU_PT_TYPE 		type;
	
	/// @brief Record the allocated memory (pages)
	XMHFList* 			used_mem;

	/// @brief the root hva address of the iommu pt
	void* 				pt_root;
} IOMMU_PT_INFO;




/********* SUBARCH Specific functions *********/
/// Invalidate the IOMMU PageTable corresponding to <pt_info>
extern void iommu_vmx_invalidate_pt(IOMMU_PT_INFO* pt_info);

/// 
extern bool iommu_vmx_map(IOMMU_PT_INFO* pt_info, gpa_t gpa, spa_t spa, uint32_t flags);

/// Bind an IOMMU PT to a device
extern bool iommu_vmx_bind_device(IOMMU_PT_INFO* pt_info, DEVICEDESC* device);

/// Bind the untrusted OS's default IOMMU PT to a device
extern bool iommu_vmx_unbind_device(DEVICEDESC* device);
#endif // __ASSEMBLY__

#endif // XMHF_DMAP