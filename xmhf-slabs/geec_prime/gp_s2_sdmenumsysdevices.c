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

#include <xmhf.h>
#include <xmhf-debug.h>
#include <xmhfgeec.h>

#include <geec_prime.h>


void gp_s2_sdmenumsysdevices(void){
    u32 b, d, f, i;
	vtd_drhd_handle_t drhd_handle;



    //as a first step, add several non-PCI system devices to the
    //sysdev list using XMHF/GEEC psuedo-PCI vendor and device IDs
    //the following are the list of non-PCI system devices:
    //LAPIC at X86SMP_LAPIC_MEMORYADDRESS (0xFEE00000)
    //TPM at TPM_LOCALITY_BASE (0xfed40000)
    //TXT at TXT_PUB_CONFIG_REGS_BASE (0xfed30000) and TXT_PRIV_CONFIG_REGS_BASE (0xfed20000)
    //SERIAL0 (used for debugging only) at DEBUG_PORT
    //IOMMU as described by vtd_drhd[]


    //sanity check available sysdev entries for the above devices
    if( (numentries_sysdev_memioregions+vtd_drhd_maxhandle+1+1+1+1) >= MAX_PLATFORM_DEVICES){
        _XDPRINTF_("%s: Halting!. numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES(%u)\n",
                   __func__, MAX_PLATFORM_DEVICES);
        HALT();
    }

    //add LAPIC device
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_LAPIC;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_LAPIC;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=X86SMP_LAPIC_MEMORYADDRESS;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=X86SMP_LAPIC_MEMORYADDRESS + PAGE_SIZE_4K;
    for(i=1; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;

    //add TPM
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_TPM;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TPM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=TPM_LOCALITY_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=TPM_LOCALITY_BASE + PAGE_SIZE_4K;
    for(i=1; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;

    //add TXT
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_TXT;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TXT;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=TXT_PRIV_CONFIG_REGS_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=TXT_PRIV_CONFIG_REGS_BASE + PAGE_SIZE_4K;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].addr_start=TXT_PUB_CONFIG_REGS_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].addr_end=TXT_PUB_CONFIG_REGS_BASE + PAGE_SIZE_4K;
    for(i=2; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;

#if defined (__DEBUG_SERIAL__)
    //add SERIAL0
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_SERIAL0;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_SERIAL0;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=DEBUG_PORT;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=DEBUG_PORT+0x8;
    for(i=1; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;
#endif

    //add IOMMU

    for(drhd_handle =0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
        sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].f=drhd_handle;
        sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_IOMMU;
        sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_IOMMU;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=vtd_drhd[drhd_handle].regbaseaddr;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=vtd_drhd[drhd_handle].regbaseaddr + PAGE_SIZE_4K;
        for(i=1; i < PCI_CONF_MAX_BARS; i++){
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
        }
        numentries_sysdev_memioregions++;
    }


    //enumerate and add rest of the system devices on the PCI bus
	for(b=0; b < PCI_BUS_MAX; b++){
		for(d=0; d < PCI_DEVICE_MAX; d++){
			for(f=0; f < PCI_FUNCTION_MAX; f++){
				u32 vendor_id, device_id;
				u32 bar_value, i;
				u8 hdr_type;
				u16 command;

				//read device and vendor ids, if no device then both will be 0xFFFF
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_VENDOR_ID, sizeof(u16), &vendor_id);
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_DEVICE_ID, sizeof(u16), &device_id);

				if(vendor_id == 0xFFFF && device_id == 0xFFFF)
					break;

                if(numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES){
                    _XDPRINTF_("%s: Halting!. numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES(%u)\n",
                               __func__, MAX_PLATFORM_DEVICES);
                    HALT();
                }

                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_HEADER_TYPE, sizeof(u8), &hdr_type);
                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), &command);

                //_XDPRINTF_("Device %x:%x:%x(%x:%x) HDR=%x, CMD=%x\n",
                //       b, d, f, vendor_id, device_id, hdr_type, command);
                sysdev_memioregions[numentries_sysdev_memioregions].b=b;
                sysdev_memioregions[numentries_sysdev_memioregions].d=d;
                sysdev_memioregions[numentries_sysdev_memioregions].f=f;
                sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=vendor_id;
                sysdev_memioregions[numentries_sysdev_memioregions].device_id=device_id;

                if(hdr_type == 0x80 || hdr_type == 0x0)
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_GENERAL;
                else if (hdr_type == 0x81 || hdr_type == 0x1)
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE;
                else
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN;

                //disable decode
                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), (command & ~(0x3)) ) ;


                //size BARs
                for(i=0; i < PCI_CONF_MAX_BARS; i++){
                    if(i >= 2 && (hdr_type == 0x81 || hdr_type == 0x1)){
                        //for PCI-to-PCI bridge devices only BAR0 and BAR1 are valid BARs
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
                    }else{
                        //for general devices BAR0-BAR5 are valid BARs
                        u32 bar_size;
                        xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_value);
                        if(bar_value){
                            if(bar_value & 0x1){ //I/O
                                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), 0xFFFFFFFFUL);
                                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_size);
                                bar_size = bar_size & ~(0x1);
                                bar_size = ~(bar_size);
                                bar_size++;

                                //_XDPRINTF_("  BAR-%u, IO, range=%x to %x\n", i,
                                //           (u16)(bar_value & ~(0x1)), (u16)((bar_value & ~(0x1)) + bar_size) ) ;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=(u16)(bar_value & ~(0x1));
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=(u16)((bar_value & ~(0x1)) + bar_size);

                           }else{
                                //memory
                                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), 0xFFFFFFFFUL);
                                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_size);
                                bar_size = bar_size & ~(0xF);
                                bar_size = ~(bar_size);
                                bar_size++;

                                //_XDPRINTF_("  BAR-%u, Mem, range=%x-%x\n", i,
                                //           (bar_value & ~(0xF)), (bar_value & ~(0xF)) + bar_size) ;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=(bar_value & ~(0xF));
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=(bar_value & ~(0xF)) + bar_size;

                            }

                            xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), bar_value);
                        }else{
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
                        }
                    }
                }


                //restore command register
                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), command);
                numentries_sysdev_memioregions++;
            }
		}
	}


    //be verbose about the system devices and their MM(IO) extents
    {
        u32 i, j;
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

}

