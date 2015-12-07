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
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>
#include <xc_init.h>

//////
// setup (unverified) slab iotbl
/////
static void _gp_setup_uhslab_iotbl_allowaccesstoport(u32 uhslabiobitmap_idx, u16 port, u16 port_size){
    u32 i;

    for(i=0; i < port_size; i++){
        u32 idx = (port+i)/8;
        u8 bit = ((port+i) % 8);
        u8 bitmask = ~((u8)1 << bit);
        gp_rwdatahdr.gp_uhslab_iobitmap[uhslabiobitmap_idx][idx] &= bitmask;
    }
}


static void gp_setup_uhslab_iotbl(u32 slabid){
	u32 j, k, portnum;

        memset(&gp_rwdatahdr.gp_uhslab_iobitmap[(slabid - XMHFGEEC_UHSLAB_BASE_IDX)], 0xFFFFFFFFUL, sizeof(gp_rwdatahdr.gp_uhslab_iobitmap[0]));

	//scan through the list of devices for this slab and add any
	//legacy I/O ports to the I/O perm. table
	for(j=0; j < _sda_slab_devicemap[slabid].device_count; j++){
	    u32 sysdev_memioregions_index = _sda_slab_devicemap[slabid].sysdev_mmioregions_indices[j];
	    for(k=0; k < PCI_CONF_MAX_BARS; k++){
		if(sysdev_memioregions[sysdev_memioregions_index].memioextents[k].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_IO){
		    for(portnum= sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_start;
			portnum < sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_end; portnum++){

			_gp_setup_uhslab_iotbl_allowaccesstoport((slabid - XMHFGEEC_UHSLAB_BASE_IDX), portnum, 1);

		    }
		}
	    }
	}
}



static void _gp_setup_ugslab_iotbl_allowaccesstoport(u32 ugslabiobitmap_idx, u16 port, u16 port_size){
    u32 i;

    for(i=0; i < port_size; i++){
        u32 idx = (port+i)/8;
        u8 bit = ((port+i) % 8);
        u8 bitmask = ~((u8)1 << bit);
        gp_rwdatahdr.gp_ugslab_iobitmap[ugslabiobitmap_idx][idx] &= bitmask;
    }
}


static void gp_setup_ugslab_iotbl(u32 slabid){
	u32 j, k, portnum;

        memset(&gp_rwdatahdr.gp_ugslab_iobitmap[(slabid - XMHFGEEC_UGSLAB_BASE_IDX)], 0xFFFFFFFFUL, sizeof(gp_rwdatahdr.gp_ugslab_iobitmap[0]));


	//scan through the list of devices for this slab and add any
	//legacy I/O ports to the I/O perm. table
	for(j=0; j < _sda_slab_devicemap[slabid].device_count; j++){
	    u32 sysdev_memioregions_index = _sda_slab_devicemap[slabid].sysdev_mmioregions_indices[j];
	    for(k=0; k < PCI_CONF_MAX_BARS; k++){
		if(sysdev_memioregions[sysdev_memioregions_index].memioextents[k].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_IO){
		    for(portnum= sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_start;
			portnum < sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_end; portnum++){

			_gp_setup_ugslab_iotbl_allowaccesstoport((slabid - XMHFGEEC_UGSLAB_BASE_IDX), portnum, 1);

		    }
		}
	    }
	}
}





void gp_s2_setupiotbl(void){
	u32 i, slabtype;


	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		if( ((xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG) ||
		    (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG)) &&
		    ((i >= XMHFGEEC_UHSLAB_BASE_IDX && i <= XMHFGEEC_UHSLAB_MAX_IDX))
		 ){
			gp_setup_uhslab_iotbl(i);


		}else if ( ((xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST) ||
			   (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST) ||
			   (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)) &&
			   ((i >= XMHFGEEC_UGSLAB_BASE_IDX && i <= XMHFGEEC_UGSLAB_MAX_IDX))
			 ){
			gp_setup_ugslab_iotbl(i);

		}else if ( ((xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ||
		   (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG)) ){
			//do nothing for verified slabs

		}else{
			//we have no idea what type of slab this is, halt!
			_XDPRINTF_("%s:%u no idea of slab %u of type %u. Halting!\n",
				__func__, __LINE__, i, xmhfgeec_slab_info_table[i].slabtype);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}

	}

	_XDPRINTF_("%s: setup unverified slab legacy I/O permission tables\n", __func__);

}

