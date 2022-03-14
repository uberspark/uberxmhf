// XMHF must separate earlyinit from runtime, because secure loader links different files from the runtime.

#include <xmhf.h>
#include "dmap-vmx-internal.h"

// maximum number of RSDT entries we support
#define ACPI_MAX_RSDT_ENTRIES (256)

//==============================================================================
// local (static) variables and function definitions
//==============================================================================

// DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd = 0; // total number of DMAR h/w units

//------------------------------------------------------------------------------
// set VT-d RET and CET tables for VT-d bootstrapping
// we have 1 root entry table (RET) of 4kb, each root entry (RE) is 128-bits
// which gives us 256 entries in the RET, each corresponding to a PCI bus num.
//(0-255)
// each RE points to a context entry table (CET) of 4kb, each context entry (CE)
// is 128-bits which gives us 256 entries in the CET, accounting for 32 devices
// with 8 functions each as per the PCI spec.
// each CE points to a PDPT type paging structure.
// we ensure that every entry in the RET is 0 which means that the DRHD will
// not allow any DMA requests for PCI bus 0-255 (Sec 3.3.2, IVTD Spec. v1.2)
// we zero out the CET just for sanity
static void _vtd_setupRETCET_bootstrap(uintptr_t vtd_ret_paddr, uintptr_t vtd_ret_vaddr, uintptr_t vtd_cet_paddr, uintptr_t vtd_cet_vaddr)
{
    // sanity check that RET and CET are page-aligned
    HALT_ON_ERRORCOND(!(vtd_ret_paddr & 0x00000FFFUL) && !(vtd_cet_paddr & 0x00000FFFUL));

    // zero out CET, we dont require it for bootstrapping
    memset((void *)vtd_cet_vaddr, 0, PAGE_SIZE_4K);

    // zero out RET, effectively preventing DMA reads and writes in the system
    memset((void *)vtd_ret_vaddr, 0, PAGE_SIZE_4K);
}

// initialize VMX EAP a.k.a VT-d
// returns 1 if all went well, else 0
// if input parameter bootstrap is 1 then we perform minimal translation
// structure initialization, else we do the full DMA translation structure
// initialization at a page-granularity
static u32 vmx_eap_initialize_early(
    spa_t vtd_pml4t_paddr, hva_t vtd_pml4t_vaddr,
    spa_t vtd_pdpt_paddr, hva_t vtd_pdpt_vaddr,
    spa_t vtd_pdts_paddr, hva_t vtd_pdts_vaddr,
    spa_t vtd_pts_paddr, hva_t vtd_pts_vaddr,
    spa_t vtd_ret_paddr, hva_t vtd_ret_vaddr,
    spa_t vtd_cet_paddr, hva_t vtd_cet_vaddr)
{
    ACPI_RSDP rsdp;
    ACPI_RSDT rsdt;
    u32 num_rsdtentries;
    uintptr_t rsdtentries[ACPI_MAX_RSDT_ENTRIES];
    uintptr_t status;
    bool status2 = false;
    VTD_DMAR dmar;
    u32 i, dmarfound;
    spa_t dmaraddrphys, remappingstructuresaddrphys;
    spa_t rsdt_xsdt_spaddr = INVALID_SPADDR;
    hva_t rsdt_xsdt_vaddr = INVALID_VADDR;

    (void)vtd_pml4t_paddr;(void)vtd_pml4t_vaddr;(void)vtd_pdpt_paddr;(void)vtd_pdpt_vaddr;
    (void)vtd_pdts_paddr;(void)vtd_pdts_vaddr;(void)vtd_pts_paddr;(void)vtd_pts_vaddr;

#ifndef __XMHF_VERIFICATION__
    // zero out rsdp and rsdt structures
    memset(&rsdp, 0, sizeof(ACPI_RSDP));
    memset(&rsdt, 0, sizeof(ACPI_RSDT));
    memset(&g_vtd_cap, 0, sizeof(struct dmap_vmx_cap));

    // get ACPI RSDP
    //  [TODO] Unify the name of <xmhf_baseplatform_arch_x86_acpi_getRSDP> and <xmhf_baseplatform_arch_x86_acpi_getRSDP>, and then remove the following #ifdef
#ifdef __X86__
    status = xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
#elif defined(__X86_64__)
    status = xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
#else
    #error "Unsupported Arch"
#endif
    HALT_ON_ERRORCOND(status != 0); // we need a valid RSDP to proceed
    printf("\n%s: RSDP at %08x", __FUNCTION__, status);

    // [Superymk] Use RSDT if it is ACPI v1, or use XSDT addr if it is ACPI v2
    if (rsdp.revision == 0) // ACPI v1
    {
        printf("\n%s: ACPI v1", __FUNCTION__);
        rsdt_xsdt_spaddr = rsdp.rsdtaddress;
    }
    else if (rsdp.revision == 0x2) // ACPI v2
    {
        printf("\n%s: ACPI v2", __FUNCTION__);
        rsdt_xsdt_spaddr = (spa_t)rsdp.xsdtaddress;
    }
    else // Unrecognized ACPI version
    {
        printf("\n%s: ACPI unsupported version!", __FUNCTION__);
        return 0;
    }

    // grab ACPI RSDT
#ifdef __X86__
    // Note: <rsdt_xsdt_spaddr> should be in lower 4GB. So the conversion to vaddr is fine.
    rsdt_xsdt_vaddr = (hva_t)rsdt_xsdt_spaddr;
#elif defined(__X86_64__)
    rsdt_xsdt_vaddr = (hva_t)rsdt_xsdt_spaddr;
#else
    #error "Unsupported Arch"
#endif

    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdt_xsdt_vaddr, sizeof(ACPI_RSDT));
    printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes",
           __FUNCTION__, rsdt_xsdt_vaddr, rsdt.length, sizeof(ACPI_RSDT));

    // get the RSDT entry list
    num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT)) / sizeof(u32);
    HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)),
                                     sizeof(rsdtentries[0]) * num_rsdtentries);
    printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
           (rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)), num_rsdtentries);

    // find the VT-d DMAR table in the list (if any)
    for (i = 0; i < num_rsdtentries; i++)
    {
        xmhf_baseplatform_arch_flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));
        if (dmar.signature == VTD_DMAR_SIGNATURE)
        {
            dmarfound = 1;
            break;
        }
    }

    // if no DMAR table, bail out
    if (!dmarfound)
        return 0;

    dmaraddrphys = rsdtentries[i]; // DMAR table physical memory address;
    printf("\n%s: DMAR at %08x", __FUNCTION__, dmaraddrphys);

    i = 0;
    remappingstructuresaddrphys = dmaraddrphys + sizeof(VTD_DMAR);
    printf("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);

    while (i < (dmar.length - sizeof(VTD_DMAR)))
    {
        u16 type, length;
        hva_t remappingstructures_vaddr = (hva_t)remappingstructuresaddrphys;

        xmhf_baseplatform_arch_flat_copy((u8 *)&type, (u8 *)(remappingstructures_vaddr + i), sizeof(u16));
        xmhf_baseplatform_arch_flat_copy((u8 *)&length, (u8 *)(remappingstructures_vaddr + i + sizeof(u16)), sizeof(u16));

        switch (type)
        {
        case 0: // DRHD
            printf("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructures_vaddr + i), length);
            HALT_ON_ERRORCOND(vtd_num_drhd < VTD_MAX_DRHD);
            xmhf_baseplatform_arch_flat_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructures_vaddr + i), length);
            vtd_num_drhd++;
            i += (u32)length;
            break;

        default: // unknown type, we skip this
            i += (u32)length;
            break;
        }
    }

    printf("\n%s: total DRHDs detected= %u units", __FUNCTION__, vtd_num_drhd);

    // be a little verbose about what we found
    printf("\n%s: DMAR Devices:", __FUNCTION__);
    for (i = 0; i < vtd_num_drhd; i++)
    {
        VTD_CAP_REG cap;
        VTD_ECAP_REG ecap;
        printf("\n	Device %u on PCI seg %04x; base=0x%016llx", i,
               vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
        _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
        printf("\n		cap=0x%016llx", (u64)cap.value);
        _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
        printf("\n		ecap=0x%016llx", (u64)ecap.value);
    }

    // Verify VT-d capabilities
    status2 = _vtd_verify_cap(vtd_drhd, vtd_num_drhd, &g_vtd_cap);
    if (!status2)
    {
        printf("\n%s: verify VT-d units' capabilities error! Halting!", __FUNCTION__);
        HALT();
    }

    // initialize VT-d RET and CET using empty RET and CET, so no DMA is allowed
    _vtd_setupRETCET_bootstrap(vtd_ret_paddr, vtd_ret_vaddr, vtd_cet_paddr, vtd_cet_vaddr);
    printf("\n%s: setup VT-d RET (%08x) and CET (%08x) for bootstrap.", __FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);

#endif //__XMHF_VERIFICATION__

#ifndef __XMHF_VERIFICATION__
    // initialize all DRHD units
    for (i = 0; i < vtd_num_drhd; i++)
    {
        printf("\n%s: initializing DRHD unit %u...", __FUNCTION__, i);
        _vtd_drhd_initialize(&vtd_drhd[i], vtd_ret_paddr);
    }
#else
    printf("\n%s: initializing DRHD unit %u...", __FUNCTION__, i);
    _vtd_drhd_initialize(&vtd_drhd[0], vtd_ret_paddr);
#endif

    // success
    printf("\n%s: success, leaving...", __FUNCTION__);

    return 1;
}

////////////////////////////////////////////////////////////////////////
// GLOBALS

//"early" DMA protection initialization to setup minimal
// structures to protect a range of physical memory
// return 1 on success 0 on failure
u32 xmhf_dmaprot_arch_x86_vmx_earlyinitialize(sla_t protectedbuffer_paddr, sla_t protectedbuffer_vaddr, size_t protectedbuffer_size, sla_t __attribute__((unused)) memregionbase_paddr, u32 __attribute__((unused)) memregion)
{
    u32 vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr, vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr;

    //(void)memregionbase_paddr;
    //(void)memregion_size;

    printf("\nSL: Bootstrapping VMX DMA protection...");

    // we use 2 pages for Vt-d bootstrapping
    HALT_ON_ERRORCOND(protectedbuffer_size >= (2 * PAGE_SIZE_4K));

    vmx_eap_vtd_ret_paddr = protectedbuffer_paddr;
    vmx_eap_vtd_ret_vaddr = protectedbuffer_vaddr;
    vmx_eap_vtd_cet_paddr = protectedbuffer_paddr + PAGE_SIZE_4K;
    vmx_eap_vtd_cet_vaddr = protectedbuffer_vaddr + PAGE_SIZE_4K;

    return vmx_eap_initialize_early(0, 0, 0, 0, 0, 0, 0, 0,
                vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr, vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr);
}
