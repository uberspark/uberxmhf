#include "iommu-pt.h"

static IOMMU_PT_INFO**   iommu_pts = NULL; // The list holding all the IOMMU_PTs, it is
// indexed with the pt handle <iommu_pt_t>
static uint32_t max_num_pts = 16; // [TODO] Use a better way to decide the <max_num_pts>

static void _pt_manager_init(void)
{
    if (iommu_pts)
        return;

    iommu_pts = xmhf_mm_malloc(max_num_pts * sizeof(IOMMU_PT_INFO*));
}

static void _pt_manager_fini(void)
{
    if (!iommu_pts)
        return;

    xmhf_mm_free(iommu_pts);
}

#define MIN_SECOS_IOMMU_PT_ID		2 // Domain ID 0 is reserved for mHV, and 1 is reserved for the rich OS
static iommu_pt_t _pt_manager_register_pt(IOMMU_PT_INFO* pt_info)
{
    uint32_t i = 0;

    for (i = MIN_SECOS_IOMMU_PT_ID; i < max_num_pts; i++)
    {
        if (!iommu_pts[i])
            break;
    }

    if (i == max_num_pts)
    {
        // no free slots
        return IOMMU_PT_INVALID;
    }

    iommu_pts[i] = pt_info;
    return (iommu_pt_t)i;
}

static IOMMU_PT_INFO* _pt_manager_unregister_pt(iommu_pt_t pt_handle)
{
    IOMMU_PT_INFO* result = NULL;

	if (pt_handle == IOMMU_PT_INVALID)
		return NULL;

    // the handle should not be larger than <max_num_pts>
    if ((uint32_t)pt_handle >= max_num_pts)
        return NULL;

    result = iommu_pts[pt_handle];
    iommu_pts[pt_handle] = NULL;

    return result;
}

static IOMMU_PT_INFO* _pt_manager_get_pt(iommu_pt_t pt_handle)
{
	if (pt_handle == IOMMU_PT_INVALID)
		return NULL;

    // the handle should not be larger than <max_num_pts>
    if ((uint32_t)pt_handle >= max_num_pts)
        return NULL;

    return iommu_pts[pt_handle];
}

static bool _iommu_pt_create_root(IOMMU_PT_INFO* pt_info)
{
    bool status = true;

    // Sanity checks
    if(!pt_info)
        return false;

    // Force allocation of the IOMMU PT root page structure.
    // [NOTE] Because IOMMU PT page structures are allocated on-demand, we can allocate the root page structure by
    // creating a dummy mapping.
    status = iommu_vmx_map(pt_info, 0, 0, DMA_DENY_ACCESS);
    return status;
}

/// @brief Initialize the IOMMU (DMA Protection to the main memory) subsystem
void xmhf_iommu_init(void)
{
    // Step 1. Init the PT manager
    _pt_manager_init();
}

/// @brief Finalize the IOMMU subsystem
void xmhf_iommu_fini(void)
{
    _pt_manager_fini();
}

uint32_t iommu_is_pt_s_exclusive(iommu_pt_t pt_handle, bool* out_result)
{
    IOMMU_PT_INFO* pt_info = NULL;

    if(pt_handle == IOMMU_PT_INVALID)
		return 1;
    if(!out_result)
		return 1;

    pt_info = _pt_manager_get_pt(pt_handle);
    if (!pt_info)
        return 1;

    if(pt_info->type == IOMMU_PT_TYPE_S_EXCLUSIVE)
        *out_result = true;
    else
        *out_result = false;

    return 0;
}

uint32_t iommu_is_pt_s_ns_shared(iommu_pt_t pt_handle, bool* out_result)
{
    IOMMU_PT_INFO* pt_info = NULL;

    if(pt_handle == IOMMU_PT_INVALID)
		return 1;
    if(!out_result)
		return 1;

    pt_info = _pt_manager_get_pt(pt_handle);
    if (!pt_info)
        return 1;

    if(pt_info->type == IOMMU_PT_TYPE_S_NS_SHARED)
        *out_result = true;
    else
        *out_result = false;

    return 0;
}

/// @brief Create a new IOMMU Page Table
iommu_pt_t xmhf_iommu_pt_create(IOMMU_PT_TYPE type)
{
    bool status = true;
    IOMMU_PT_INFO* pt_info = NULL;
    iommu_pt_t pt_handle = IOMMU_PT_INVALID;

    // Step 1. Initialize <pt_info>
    pt_info = (IOMMU_PT_INFO*)xmhf_mm_malloc(sizeof(IOMMU_PT_INFO));
    pt_info->used_mem = xmhfstl_list_create();

    // Step 2. Register the new PT in the system, and returns its handle
    pt_handle = _pt_manager_register_pt(pt_info);
    if (pt_handle == IOMMU_PT_INVALID)
    {
        // The IOMMU cannot load more PTs, so we should destroy the allocated
        // structures.
        if (pt_info->used_mem)
            xmhfstl_list_clear_destroy(pt_info->used_mem);
        xmhf_mm_free(pt_info);
    }
	pt_info->iommu_pt_id = pt_handle;
    pt_info->type = type;

    // Allocate the IOMMU PT root page structure, so we can bind the IOMMU PT to the device after creating the PT.
    status = _iommu_pt_create_root(pt_info);
    if(!status)
    {
        xmhf_iommu_pt_destroy(pt_handle);
        return IOMMU_PT_INVALID;
    }

    return pt_handle;
}

/// @brief Destroy an IOMMU Page Table
bool xmhf_iommu_pt_destroy(iommu_pt_t pt_handle)
{
    IOMMU_PT_INFO* pt_info = NULL;

	if(pt_handle == IOMMU_PT_INVALID)
		return true;

    // Step 1. Search the corresponding <pt_info>
    pt_info = _pt_manager_unregister_pt(pt_handle);
    if (!pt_info)
        return false;

    // Step 2. Destroy the <pt_info>
    if (pt_info->used_mem)
    {
    	xmhf_mm_free_all_records(pt_info->used_mem);
        pt_info->used_mem = NULL;
    }

	pt_info->iommu_pt_id = IOMMU_PT_INVALID;
    pt_info->type = IOMMU_PT_TYPE_INVALID;
    xmhf_mm_free(pt_info);

    return true;
}

/*bool xmhf_iommu_pt_map(iommu_pt_t pt_handle, gpa_t start_gpa, spa_t start_spa, uint32_t num_pages, uint32_t flags)
{
    IOMMU_PT_INFO* pt_info = NULL;
    bool status = false;

    pt_info = _pt_manager_get_pt(pt_handle);
    if (!pt_info)
        return false;

    status = iommu_vmx_map(pt_info, start_gpa, start_gpa, num_pages, flags);

    iommu_vmx_invalidate_pt(pt_info);
    return status;
}

bool xmhf_iommu_pt_map_batch(iommu_pt_t pt_handle, gpa_t start_gpa, spa_t* spas, uint32_t num_pages, uint32_t flags)
{
    IOMMU_PT_INFO* pt_info = NULL;
    bool status = false;

    pt_info = _pt_manager_get_pt(pt_handle);
    if (!pt_info)
        return false;

    status = iommu_vmx_map_batch(pt_info, start_gpa, spas, num_pages, flags);

    iommu_vmx_invalidate_pt(pt_info);
    return status;
}*/



/// @brief Map <spa> with <gpa> in the IOMMU PT
bool xmhf_iommu_pt_map(iommu_pt_t pt_handle, gpa_t gpa, spa_t spa, uint32_t flags)
{
	IOMMU_PT_INFO* pt_info = NULL;
    bool status = false;

    pt_info = _pt_manager_get_pt(pt_handle);
    if (!pt_info)
        return false;

    // Check: The function must not map mhv's memory, even if <flags> specify deny accesses.
    if(xmhf_is_mhv_memory(spa))
        return false;

    // printf("<xmhf_iommu_pt_map> pt_handle:%u, gpa:%#X, spa:%#X, flags:%u\n",
	// 			pt_handle, gpa, spa, flags);
    status = iommu_vmx_map(pt_info, gpa, spa, flags);
    return status;
}

/// @brief Load the IOMMU PT for a specific device
bool xmhf_iommu_bind_device(iommu_pt_t pt_handle, DEVICEDESC* device)
{
    IOMMU_PT_INFO* pt_info = NULL;
    bool status = false;

    pt_info = _pt_manager_get_pt(pt_handle);
    if (!pt_info)
        return false;

    status = iommu_vmx_bind_device(pt_info, device);

	// Flush the IOMMU PT to the main memory
	wbinvd();

    xmhf_dmaprot_invalidate_cache();
    return status;
}

/// @brief Bind the untrusted OS's default IOMMU PT to the specific device
bool xmhf_iommu_unbind_device(DEVICEDESC* device)
{
    bool status = false;

    status = iommu_vmx_unbind_device(device);

	// Flush the IOMMU PT to the main memory
	wbinvd();

    xmhf_dmaprot_invalidate_cache();
    return status;
}

// [TODO-Important] Do we need this function?
/// @brief Map <spa> with <gpa> in all IOMMU_PT_TYPE_S_NS_SHARED IOMMU PTs.
/// [NOTE] This function is needed when moving memory between S and NS domains. Otherwise, a shared IOMMU PT created
/// by a SecProcess ealier may map isolated memory given to other SecProcesses later. This violates memory separation
/// between SecProcesses.
/// [TODO][Issue 60] SecBase needs to prove: All IOMMU_PT_TYPE_S_NS_SHARED IOMMU PTs map NS domain's memory and given
/// S domain's memory, but not any other S domain's memory.
bool xmhf_iommu_all_shared_pts_map(gpa_t gpa, uint32_t flags)
{
    uint32_t i = 0;

    for (i = MIN_SECOS_IOMMU_PT_ID; i < max_num_pts; i++)
    {
        bool status = false;
        IOMMU_PT_INFO* pt_info = iommu_pts[i];

        if (!pt_info)
            continue;

        if(pt_info->type == IOMMU_PT_TYPE_S_NS_SHARED)
        {
            status = xmhf_iommu_pt_map(pt_info->iommu_pt_id, gpa, (spa_t)gpa, flags);
            if(!status)
            {
                printf("Update mappings of all shared IOMMU PTs error: pt_handle:%u, gpa:%#X, flags:%u\n",
	 			    pt_info->iommu_pt_id, gpa, flags);
                return false;
            }
        }
    }

    return true;
}
