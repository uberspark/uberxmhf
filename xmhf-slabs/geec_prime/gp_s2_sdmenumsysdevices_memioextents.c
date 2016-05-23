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


void gp_s2_sdmenumsysdevices_memioextents(u32 sysdev_memioregions_index, u32 b, u32 d, u32 f, u32 vendor_id, u32 device_id){
	u32 i;

    sysdev_memioregions[sysdev_memioregions_index].b=b;
    sysdev_memioregions[sysdev_memioregions_index].d=d;
    sysdev_memioregions[sysdev_memioregions_index].f=f;
    sysdev_memioregions[sysdev_memioregions_index].vendor_id=vendor_id;
    sysdev_memioregions[sysdev_memioregions_index].device_id=device_id;

    if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_LAPIC){
        sysdev_memioregions[sysdev_memioregions_index].dtype = SYSDEV_MEMIOREGIONS_DTYPE_LAPIC;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_start=X86SMP_LAPIC_MEMORYADDRESS;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_end=X86SMP_LAPIC_MEMORYADDRESS + PAGE_SIZE_4K;
        for(i=1; i < PCI_CONF_MAX_BARS; i++){
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=0;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=0;
        }

    }else if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_TPM){
        sysdev_memioregions[sysdev_memioregions_index].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TPM;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_start=TPM_LOCALITY_BASE;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_end=TPM_LOCALITY_BASE + PAGE_SIZE_4K;
        for(i=1; i < PCI_CONF_MAX_BARS; i++){
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=0;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=0;
        }


    }else if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_TXT){
        sysdev_memioregions[sysdev_memioregions_index].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TXT;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_start=TXT_PRIV_CONFIG_REGS_BASE;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_end=TXT_PRIV_CONFIG_REGS_BASE + PAGE_SIZE_4K;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[1].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[1].addr_start=TXT_PUB_CONFIG_REGS_BASE;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[1].addr_end=TXT_PUB_CONFIG_REGS_BASE + PAGE_SIZE_4K;
        for(i=2; i < PCI_CONF_MAX_BARS; i++){
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=0;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=0;
        }


#if defined (__DEBUG_SERIAL__)
    }else if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_SERIAL0){
        sysdev_memioregions[sysdev_memioregions_index].dtype = SYSDEV_MEMIOREGIONS_DTYPE_SERIAL0;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_start=DEBUG_PORT;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_end=DEBUG_PORT+0x8;
        for(i=1; i < PCI_CONF_MAX_BARS; i++){
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=0;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=0;
        }
#endif //__DEBUG_SERIAL


    }else if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_IOMMU){
        sysdev_memioregions[sysdev_memioregions_index].dtype = SYSDEV_MEMIOREGIONS_DTYPE_IOMMU;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_start=vtd_drhd[f].regbaseaddr;
        sysdev_memioregions[sysdev_memioregions_index].memioextents[0].addr_end=vtd_drhd[f].regbaseaddr + PAGE_SIZE_4K;
        for(i=1; i < PCI_CONF_MAX_BARS; i++){
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=0;
            sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=0;
        }


    }else{
		u32 bar_value;
		u8 hdr_type;
		u16 command;

    	xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_HEADER_TYPE, sizeof(u8), &hdr_type);
        xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), &command);

        //_XDPRINTF_("Device %x:%x:%x(%x:%x) HDR=%x, CMD=%x\n",
        //       b, d, f, vendor_id, device_id, hdr_type, command);

        if(hdr_type == 0x80 || hdr_type == 0x0)
            sysdev_memioregions[sysdev_memioregions_index].dtype=SYSDEV_MEMIOREGIONS_DTYPE_GENERAL;
        else if (hdr_type == 0x81 || hdr_type == 0x1)
            sysdev_memioregions[sysdev_memioregions_index].dtype=SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE;
        else
            sysdev_memioregions[sysdev_memioregions_index].dtype=SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN;

        //disable decode
        xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), (command & ~(0x3)) ) ;


        //size BARs
        for(i=0; i < PCI_CONF_MAX_BARS; i++){
            if(i >= 2 && (hdr_type == 0x81 || hdr_type == 0x1)){
                //for PCI-to-PCI bridge devices only BAR0 and BAR1 are valid BARs
                sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
                sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=0;
                sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=0;
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
                        sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
                        sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=(u16)(bar_value & ~(0x1));
                        sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=(u16)((bar_value & ~(0x1)) + bar_size);

                   }else{
                        //memory
                        xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), 0xFFFFFFFFUL);
                        xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_size);
                        bar_size = bar_size & ~(0xF);
                        bar_size = ~(bar_size);
                        bar_size++;

                        //_XDPRINTF_("  BAR-%u, Mem, range=%x-%x\n", i,
                        //           (bar_value & ~(0xF)), (bar_value & ~(0xF)) + bar_size) ;
                        sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
                        sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=(bar_value & ~(0xF));
                        sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=(bar_value & ~(0xF)) + bar_size;

                    }

                    xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), bar_value);
                }else{
                    sysdev_memioregions[sysdev_memioregions_index].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
                    sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_start=0;
                    sysdev_memioregions[sysdev_memioregions_index].memioextents[i].addr_end=0;
                }
            }
        }


		//restore command register
		xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), command);
    }
}
