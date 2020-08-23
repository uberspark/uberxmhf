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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
// #include <xmhfgeec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>

/*@
	requires 0 <= vtd_drhd_maxhandle <= VTD_MAX_DRHD;
	ensures 0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES;
@*/
void gp_s2_sdmenumsysdevices(void){
    uint32_t b, d, f, i;
	vtd_drhd_handle_t drhd_handle;
	uint32_t vendor_id, device_id;

    //as a first step, add several non-PCI system devices to the
    //sysdev list using XMHF/GEEC psuedo-PCI vendor and device IDs
    //the following are the list of non-PCI system devices:
    //LAPIC at X86SMP_LAPIC_MEMORYADDRESS (0xFEE00000)
    //TPM at TPM_LOCALITY_BASE (0xfed40000)
    //TXT at TXT_PUB_CONFIG_REGS_BASE (0xfed30000) and TXT_PRIV_CONFIG_REGS_BASE (0xfed20000)
    //SERIAL0 (used for debugging only) at DEBUG_PORT
    //IOMMU as described by vtd_drhd[]

	//add LAPIC device
	gp_s2_sdmenumsysdevices_memioextents(PCI_BUS_XMHFGEEC, PCI_DEVICE_XMHFGEEC, 0, PCI_VENDOR_ID_XMHFGEEC, PCI_DEVICE_ID_XMHFGEEC_LAPIC);

	//add TPM
	gp_s2_sdmenumsysdevices_memioextents(PCI_BUS_XMHFGEEC, PCI_DEVICE_XMHFGEEC, 0, PCI_VENDOR_ID_XMHFGEEC, PCI_DEVICE_ID_XMHFGEEC_TPM);

	//add TXT
	gp_s2_sdmenumsysdevices_memioextents(PCI_BUS_XMHFGEEC, PCI_DEVICE_XMHFGEEC, 0, PCI_VENDOR_ID_XMHFGEEC, PCI_DEVICE_ID_XMHFGEEC_TXT);

	#if defined (__DEBUG_SERIAL__)
		//add SERIAL0
	gp_s2_sdmenumsysdevices_memioextents(PCI_BUS_XMHFGEEC, PCI_DEVICE_XMHFGEEC, 0, PCI_VENDOR_ID_XMHFGEEC, PCI_DEVICE_ID_XMHFGEEC_SERIAL0);
	#endif

	//add IOMMU
	/*@
		loop invariant a1: 0 <= drhd_handle <= vtd_drhd_maxhandle;
		loop assigns drhd_handle;
		loop variant vtd_drhd_maxhandle - drhd_handle;
	@*/
	for(drhd_handle =0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		gp_s2_sdmenumsysdevices_memioextents(PCI_BUS_XMHFGEEC, PCI_DEVICE_XMHFGEEC, drhd_handle, PCI_VENDOR_ID_XMHFGEEC, PCI_DEVICE_ID_XMHFGEEC_IOMMU);
	}


    //enumerate and add rest of the system devices on the PCI bus
	/*@
		loop invariant b1: 0 <= b <= PCI_BUS_MAX;
		loop assigns b;
		loop assigns d;
		loop assigns f;
		loop assigns vendor_id;
		loop assigns device_id;
		loop variant PCI_BUS_MAX - b;
	@*/
	for(b=0; b < PCI_BUS_MAX; b++){

		/*@
			loop invariant b2: 0 <= d <= PCI_DEVICE_MAX;
			loop assigns d;
			loop assigns f;
			loop assigns vendor_id;
			loop assigns device_id;
			loop variant PCI_DEVICE_MAX - d;
		@*/
		for(d=0; d < PCI_DEVICE_MAX; d++){

			/*@
				loop invariant b3: 0 <= f <= PCI_FUNCTION_MAX;
				loop assigns f;
				loop assigns vendor_id;
				loop assigns device_id;
				loop variant PCI_FUNCTION_MAX - f;
			@*/
			for(f=0; f < PCI_FUNCTION_MAX; f++){
				//read device and vendor ids, if no device then both will be 0xFFFF
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_VENDOR_ID, sizeof(uint16_t), &vendor_id);
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_DEVICE_ID, sizeof(uint16_t), &device_id);

				if( !(vendor_id == 0xFFFF && device_id == 0xFFFF) ){
	                gp_s2_sdmenumsysdevices_memioextents(b, d, f, vendor_id, device_id);
				}
            }
		}
	}


#if defined (__DEBUG_SERIAL__)

    //be verbose about the system devices and their MM(IO) extents
    {
        uint32_t i, j;
        for(i=0; i <numentries_sysdev_memioregions; i++){
            _XDPRINTF_("Device idx=%u, %x:%x:%x (vid:did=%x:%x, type=%x)...\n", i, sysdev_memioregions[i].b,
                       sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                       sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype);
            for(j=0; j < PCI_CONF_MAX_BARS; j++){
                switch(sysdev_memioregions[i].memioextents[j].extent_type){
                    case _MEMIOREGIONS_EXTENTS_TYPE_IO:
                        _XDPRINTF_("  IO region: %x - %x\n", sysdev_memioregions[i].memioextents[j].addr_start,
                                        sysdev_memioregions[i].memioextents[j].addr_end);
                        break;

                    case _MEMIOREGIONS_EXTENTS_TYPE_MEM:
                        _XDPRINTF_("  MEM region: %x - %x\n", sysdev_memioregions[i].memioextents[j].addr_start,
                                        sysdev_memioregions[i].memioextents[j].addr_end);
                        break;

                    default:
                        break;
                }
            }
        }
    }
#endif // __DEBUG_SERIAL__

}

