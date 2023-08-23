/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

/**
 * rntm-x86-dmap.c
 * DMA related functions that are needed even DMAP is off.
 * author: Eric Li (xiaoyili@andrew.cmu.edu)
 */

#include <xmhf.h>

#if defined(__DRT__) || defined(__DMAP__)

/* Maximum number of RSDT entries we support */
#define ACPI_MAX_RSDT_ENTRIES (256)

/* Size of ACPI DESCRIPTION_HEADER Fields */
#define ACPI_DESC_HEADER_SIZE 36

/* Offset of interesting DESCRIPTION_HEADER fields */
#define ACPI_DESC_SIGNATURE_OFF 0
#define ACPI_DESC_LENGTH_OFF 4
#define ACPI_DESC_CHECKSUM_OFF 9

/*
 * Given the address of ACPI DMAR table, change it to something else so that
 * the red OS thinks there is no DMAR table present. Currently changing to a
 * table with signature "XMHF".
 */
void vmx_dmar_zap(spa_t dmaraddrphys)
{
	u8 buffer[ACPI_DESC_HEADER_SIZE];
	u8 checksum = 0;
	/* Signature: "XMHF" */
	xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys + ACPI_DESC_SIGNATURE_OFF, 0x46484d58UL);
	/* Length: 36 */
	xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys + ACPI_DESC_LENGTH_OFF, 36UL);
	/* Compute checksum */
	xmhf_baseplatform_arch_flat_copy(buffer, (u8 *)(uintptr_t)dmaraddrphys, ACPI_DESC_HEADER_SIZE);
	buffer[ACPI_DESC_CHECKSUM_OFF] = 0;
	for (size_t i = 0; i < ACPI_DESC_HEADER_SIZE; i++) {
		checksum -= buffer[i];
	}
	xmhf_baseplatform_arch_flat_writeu8(dmaraddrphys + ACPI_DESC_CHECKSUM_OFF, checksum);
}

/*
 * Return the physical address of ACPI DMAR table. Return 0 if not found.
 * If found, the beginning of the DMAR table is written to dmar.
 */
spa_t vmx_find_dmar_paddr(VTD_DMAR *dmar)
{
    ACPI_RSDP rsdp;
    ACPI_RSDT rsdt;
    u32 num_rsdtentries;
    uintptr_t status;
    u32 i, dmarfound = 0;
    spa_t dmaraddrphys;
    spa_t rsdt_xsdt_spaddr = INVALID_SPADDR;
    hva_t rsdt_xsdt_vaddr = INVALID_VADDR;
    u32 rsdt_xsdt_entry_size = 0;

    // zero out rsdp and rsdt structures
    memset(&rsdp, 0, sizeof(ACPI_RSDP));
    memset(&rsdt, 0, sizeof(ACPI_RSDT));

    // get ACPI RSDP
    status = xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
    HALT_ON_ERRORCOND(status != 0); // we need a valid RSDP to proceed
    printf("%s: RSDP at %lx\n", __FUNCTION__, status);

    // Use RSDT if it is ACPI v1, or use XSDT addr if it is ACPI v2
    if (rsdp.revision == 0) // ACPI v1
    {
        printf("%s: ACPI v1\n", __FUNCTION__);
        rsdt_xsdt_spaddr = rsdp.rsdtaddress;
        rsdt_xsdt_entry_size = 4;
    }
    else if (rsdp.revision == 0x2) // ACPI v2
    {
        printf("%s: ACPI v2\n", __FUNCTION__);
        rsdt_xsdt_spaddr = (spa_t)rsdp.xsdtaddress;
        rsdt_xsdt_entry_size = 8;
    }
    else // Unrecognized ACPI version
    {
        printf("%s: ACPI unsupported version!\n", __FUNCTION__);
        return 0;
    }

    // grab ACPI RSDT
    // Note: in i386, <rsdt_xsdt_spaddr> should be in lower 4GB. So the conversion to vaddr is fine.
    rsdt_xsdt_vaddr = (hva_t)rsdt_xsdt_spaddr;

    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdt_xsdt_vaddr, sizeof(ACPI_RSDT));
    printf("%s: RSDT at %lx, len=%u bytes, hdrlen=%u bytes\n",
           __FUNCTION__, rsdt_xsdt_vaddr, rsdt.length, sizeof(ACPI_RSDT));

    // get the RSDT entry list
    num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT)) / rsdt_xsdt_entry_size;
    HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
    printf("%s: RSDT entry list at %lx, len=%u\n", __FUNCTION__,
           (rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)), num_rsdtentries);

    // find the VT-d DMAR table in the list (if any)
    for (i = 0; i < num_rsdtentries; i++)
    {
        u32 signature;
        // Read RSDT / XSDT entry
        // dmaraddrphys must be initialized to 0 because sizeof(spa_t) = 8 and
        // it is possible that rsdt_xsdt_entry_size = 4.
        dmaraddrphys = 0;
        xmhf_baseplatform_arch_flat_copy((u8 *)&dmaraddrphys,
                                         (u8 *)(rsdt_xsdt_vaddr +
                                                sizeof(ACPI_RSDT) +
                                                i * rsdt_xsdt_entry_size),
                                         rsdt_xsdt_entry_size);
        // Read first 4 bytes of the table (signature)
        xmhf_baseplatform_arch_flat_copy((u8 *)&signature,
                                         (u8 *)(uintptr_t)dmaraddrphys,
                                         sizeof(signature));
        if (signature == VTD_DMAR_SIGNATURE)
        {
            dmarfound = 1;
            break;
        }
    }

    // if no DMAR table, bail out
    if (!dmarfound)
        return 0;

    printf("%s: DMAR at %08x\n", __FUNCTION__, dmaraddrphys);

    // Read DMAR out, check length
    xmhf_baseplatform_arch_flat_copy((u8 *)dmar, (u8 *)(uintptr_t)dmaraddrphys,
                                     sizeof(VTD_DMAR));
    HALT_ON_ERRORCOND(dmar->length >= ACPI_DESC_HEADER_SIZE);

    return dmaraddrphys;
}

#endif /* defined(__DRT__) || defined(__DMAP__) */

#if defined(__DRT__) && !defined(__DMAP__)

void vmx_eap_zap(void)
{
    VTD_DMAR dmar;
    spa_t dmaraddrphys = vmx_find_dmar_paddr(&dmar);
    if (dmaraddrphys == 0) {
        return;
    }

    // zap VT-d presence in ACPI table...
    // TODO: we need to be a little elegant here. eventually need to setup
    // EPT/NPTs such that the DMAR pages are unmapped for the guest
    vmx_dmar_zap(dmaraddrphys);

    // success
    printf("%s: success, leaving...\n", __FUNCTION__);
}

#endif /* defined(__DRT__) && !defined(__DMAP__) */

