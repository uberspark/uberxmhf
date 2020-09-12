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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>


//@ghost bool gp_s2_sdmenumsysdevices_memioextents_syshalt = false;
/*@

	behavior addentry:
		assumes (numentries_sysdev_memioregions < MAX_PLATFORM_DEVICES);

		assigns numentries_sysdev_memioregions;
		assigns gp_s2_sdmenumsysdevices_memioextents_syshalt;
		assigns sysdev_memioregions[\at(numentries_sysdev_memioregions, Pre)];

		ensures (numentries_sysdev_memioregions == (\at(numentries_sysdev_memioregions, Pre) + 1));
		ensures (0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES);
		ensures (gp_s2_sdmenumsysdevices_memioextents_syshalt == false);

	behavior invalidhalt:
		assumes (numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES);

		assigns gp_s2_sdmenumsysdevices_memioextents_syshalt;

		ensures (gp_s2_sdmenumsysdevices_memioextents_syshalt == true);

	complete behaviors;
	disjoint behaviors;
@*/
void gp_s2_sdmenumsysdevices_memioextents(uint32_t b, uint32_t d, uint32_t f, uint32_t vendor_id, uint32_t device_id){
	uint32_t i;
	uint32_t bar_value;
	uint32_t hdr_type;
	uint32_t command;
	uint32_t bar_size;

    if( numentries_sysdev_memioregions < MAX_PLATFORM_DEVICES){

		sysdev_memioregions[numentries_sysdev_memioregions].b=b;
		sysdev_memioregions[numentries_sysdev_memioregions].d=d;
		sysdev_memioregions[numentries_sysdev_memioregions].f=f;
		sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=vendor_id;
		sysdev_memioregions[numentries_sysdev_memioregions].device_id=device_id;


		if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_LAPIC){
			sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_LAPIC;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=X86SMP_LAPIC_MEMORYADDRESS;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=X86SMP_LAPIC_MEMORYADDRESS + PAGE_SIZE_4K;
			/*@
				loop invariant a1: 1 <= i <= PCI_CONF_MAX_BARS;
				loop assigns i;
				loop assigns sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1..(PCI_CONF_MAX_BARS-1)];
				loop variant PCI_CONF_MAX_BARS - i;
			@*/
			for(i=1; i < PCI_CONF_MAX_BARS; i++){
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
			}


		}else if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_TPM){
			sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TPM;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=TPM_LOCALITY_BASE;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=TPM_LOCALITY_BASE + PAGE_SIZE_4K;
			/*@
				loop invariant a2: 1 <= i <= PCI_CONF_MAX_BARS;
				loop assigns i;
				loop assigns sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1..(PCI_CONF_MAX_BARS-1)];
				loop variant PCI_CONF_MAX_BARS - i;
			@*/
			for(i=1; i < PCI_CONF_MAX_BARS; i++){
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
			}


		}else if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_TXT){
			sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TXT;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=TXT_PRIV_CONFIG_REGS_BASE;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=TXT_PRIV_CONFIG_REGS_BASE + PAGE_SIZE_4K;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].addr_start=TXT_PUB_CONFIG_REGS_BASE;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].addr_end=TXT_PUB_CONFIG_REGS_BASE + PAGE_SIZE_4K;
			/*@
				loop invariant a3: 2 <= i <= PCI_CONF_MAX_BARS;
				loop assigns i;
				loop assigns sysdev_memioregions[numentries_sysdev_memioregions].memioextents[2..(PCI_CONF_MAX_BARS-1)];
				loop variant PCI_CONF_MAX_BARS - i;
			@*/
			for(i=2; i < PCI_CONF_MAX_BARS; i++){
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
			}


		#if defined (__DEBUG_SERIAL__)
		}else if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_SERIAL0){
			sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_SERIAL0;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=DEBUG_PORT;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=DEBUG_PORT+0x8;
			for(i=1; i < PCI_CONF_MAX_BARS; i++){
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
			}
		#endif //__DEBUG_SERIAL


		}else if(vendor_id == PCI_VENDOR_ID_XMHFGEEC && device_id == PCI_DEVICE_ID_XMHFGEEC_IOMMU){
			sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_IOMMU;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=vtd_drhd[f].regbaseaddr;
			sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=vtd_drhd[f].regbaseaddr + PAGE_SIZE_4K;
			/*@
				loop invariant a4: 1 <= i <= PCI_CONF_MAX_BARS;
				loop assigns i;
				loop assigns sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1..(PCI_CONF_MAX_BARS-1)];
				loop variant PCI_CONF_MAX_BARS - i;
			@*/
			for(i=1; i < PCI_CONF_MAX_BARS; i++){
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
				sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
			}


		}else{

			xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_HEADER_TYPE, sizeof(uint8_t), &hdr_type);
			xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(uint16_t), &command);

			//_XDPRINTF_("Device %x:%x:%x(%x:%x) HDR=%x, CMD=%x\n",
			//       b, d, f, vendor_id, device_id, hdr_type, command);

			if(hdr_type == 0x80 || hdr_type == 0x0)
				sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_GENERAL;
			else if (hdr_type == 0x81 || hdr_type == 0x1)
				sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE;
			else
				sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN;

			//disable decode
			xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(uint16_t), (command & ~(0x3)) ) ;


			//size BARs
			/*@
				loop invariant a5: 0 <= i <= PCI_CONF_MAX_BARS;
				loop assigns i;
				loop assigns bar_size;
				loop assigns bar_value;
				loop assigns sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0..(PCI_CONF_MAX_BARS-1)];
				loop variant PCI_CONF_MAX_BARS - i;
			@*/
			for(i=0; i < PCI_CONF_MAX_BARS; i++){
				if(i >= 2 && (hdr_type == 0x81 || hdr_type == 0x1)){
					//for PCI-to-PCI bridge devices only BAR0 and BAR1 are valid BARs
					sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
					sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
					sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
				}else{
					//for general devices BAR0-BAR5 are valid BARs
					xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(uint32_t), &bar_value);
					if(bar_value){
						if(bar_value & 0x1){ //I/O
							xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(uint32_t), 0xFFFFFFFFUL);
							xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(uint32_t), &bar_size);
							bar_size = bar_size & ~(0x1);
							bar_size = ~(bar_size);
							bar_size++;

							//_XDPRINTF_("  BAR-%u, IO, range=%x to %x\n", i,
							//           (uint16_t)(bar_value & ~(0x1)), (uint16_t)((bar_value & ~(0x1)) + bar_size) ) ;
							sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
							sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=(uint16_t)(bar_value & ~(0x1));
							sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=(uint16_t)((bar_value & ~(0x1)) + bar_size);

					   }else{
							//memory
							xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(uint32_t), 0xFFFFFFFFUL);
							xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(uint32_t), &bar_size);
							bar_size = bar_size & ~(0xF);
							bar_size = ~(bar_size);
							bar_size++;

							//_XDPRINTF_("  BAR-%u, Mem, range=%x-%x\n", i,
							//           (bar_value & ~(0xF)), (bar_value & ~(0xF)) + bar_size) ;
							sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
							sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=(bar_value & ~(0xF));
							sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=(bar_value & ~(0xF)) + bar_size;

						}

						xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(uint32_t), bar_value);
					}else{
						sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
						sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
						sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
					}
				}
			}


			//restore command register
			xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(uint16_t), command);
		}

		numentries_sysdev_memioregions++;
        //@ghost gp_s2_sdmenumsysdevices_memioextents_syshalt = false;

    }else{

		_XDPRINTF_("%s: Halting!. numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES(%u)\n",
                   __func__, MAX_PLATFORM_DEVICES);
        CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
        //@ghost gp_s2_sdmenumsysdevices_memioextents_syshalt = true;

	}
}
