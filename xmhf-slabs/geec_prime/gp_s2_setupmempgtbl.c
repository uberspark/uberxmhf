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







#if 1
// /*@
//   //requires n >= 0;
// 	assigns \nothing;
// 	ensures 0 <= \result < PAGE_SIZE_4K;
// @*/
//static u64 _geec_prime_slab_getptflagsforspa_pae(u32 slabid, u32 spa, u32 spatype);
#endif // 0




/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	requires \forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
	requires 0 <= _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
	assigns \nothing;
	ensures (\result == true) || (\result == false) ;
	ensures (\forall u32 x, u32 y; ( (0 <= x < _sda_slab_devicemap[slabid].device_count) &&
					   (0 <= y < PCI_CONF_MAX_BARS) ) ==> !(sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM &&
			(spa >= sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].addr_start &&
			    spa < sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].addr_end) )) ==> 	(\result == false);

@*/
static bool _geec_prime_smt_slab_getspatype_isdevicemmio(u32 slabid, u32 spa);




/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	assigns \nothing;
	behavior memsys:
                assumes ( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER)
		  );
		ensures (\result == (u64)(_PAGE_PRESENT | _PAGE_RW) );

	behavior memcode:
		assumes ( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    !((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER) &&
		    ( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || ((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG) ||
			((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ) &&
		    ( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_CODE )
		  );
		ensures (\result == (u64)(_PAGE_PRESENT) );

	behavior memdatastackdmadataiotbl:
		assumes ( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    !((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER) &&
		    ( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || ((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG) ||
			((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ) &&
		    !( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_CODE ) &&
		    ( ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DATA) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_STACK) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DMADATA) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_GEEC_PRIME_IOTBL)
  	            )
		  );
                ensures (\result == (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_NX) );

	behavior memdevice:
                assumes ( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    !((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER) &&
		    ( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || ((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG) ||
			((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ) &&
		    !( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_CODE ) &&
		    !( ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DATA) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_STACK) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DMADATA) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_GEEC_PRIME_IOTBL)
  	            ) &&
		    ( ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DEVICEMMIO) )
		  );
		ensures (\result == (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_NX | _PAGE_PCD) );

	behavior memotheruvslab:
		assumes ( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    !((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER) &&
		    !( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || ((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG) ||
			((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL) )
		  );
		ensures (\result == (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_NX) );

	behavior error:
		assumes !( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER)
		  );
		assumes !( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    !((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER) &&
		    ( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || ((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG) ||
			((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ) &&
		    ( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_CODE )
		  );
		assumes !( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    !((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER) &&
		    ( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || ((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG) ||
			((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ) &&
		    !( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_CODE ) &&
		    ( ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DATA) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_STACK) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DMADATA) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_GEEC_PRIME_IOTBL)
  	            )
		  );
                assumes !( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    !((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER) &&
		    ( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || ((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG) ||
			((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ) &&
		    !( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_CODE ) &&
		    !( ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DATA) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_STACK) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DMADATA) ||
		      ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_GEEC_PRIME_IOTBL)
  	            ) &&
		    ( ((spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DEVICEMMIO) )
		  );
		assumes !( (xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG) &&
		    !((spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER) &&
		    !( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || ((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG) ||
			((spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL) )
		  );
		ensures (\result == 0);

	complete behaviors;
	disjoint behaviors;


@*/
static u64 gp_vhslab_mempgtl_getptflagsforspa_pae(u32 slabid, u32 spa, u32 spatype);






//done
#if 1
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	requires \forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
	requires 0 <= _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
	assigns \nothing;
	ensures (\result == true) || (\result == false) ;
	ensures (\forall u32 x, u32 y; ( (0 <= x < _sda_slab_devicemap[slabid].device_count) &&
					   (0 <= y < PCI_CONF_MAX_BARS) ) ==> !(sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM &&
			(spa >= sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].addr_start &&
			    spa < sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].addr_end) )) ==> 	(\result == false);

@*/
static bool _geec_prime_smt_slab_getspatype_isdevicemmio(u32 slabid, u32 spa){
    u32 i, j;

	/*@
		loop invariant c1: 0 <= i <= _sda_slab_devicemap[slabid].device_count;
		loop assigns i, j;
		loop variant _sda_slab_devicemap[slabid].device_count - i;
	@*/
	for(i=0; i < _sda_slab_devicemap[slabid].device_count; i++){

		/*@
			loop invariant c2: 0 <= j <= PCI_CONF_MAX_BARS;
			loop invariant c3: \forall integer x; 0 <= x < j ==> (!(sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[x].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM &&
			(spa >= sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[x].addr_start &&
			    spa < sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[x].addr_end) ));
			loop assigns j;
			loop variant PCI_CONF_MAX_BARS - j;
		@*/
		for(j=0; j < PCI_CONF_MAX_BARS; j++){
		    if(sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[j].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM &&
			(spa >= sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[j].addr_start &&
			    spa < sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[j].addr_end) )
			    return true;
		}
	}

    return false;
}
#endif // 0



//done
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	assigns \nothing;
	behavior isiotbl:
		assumes (\forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
			spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) );
		ensures	(\result == false);
	behavior isnotiotbl:
		assumes !(\forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
			spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) );
		ensures	(\result == true);
	complete  behaviors;
	disjoint behaviors;
	//ensures (\result == true) || (\result == false);
	//ensures (\forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
	//  spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) ) ==> 	(\result == false);
	//ensures !(\forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
	//  spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) ) ==> 	(\result == true);
@*/
static bool _geec_prime_smt_slab_getspatype_isiotbl(u32 slabid, u32 spa);

#if 1
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	assigns \nothing;
	behavior isiotbl:
		assumes (\forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
			spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) );
		ensures	(\result == false);
	behavior isnotiotbl:
		assumes !(\forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
			spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) );
		ensures	(\result == true);
	complete  behaviors;
	disjoint behaviors;
	//ensures (\result == true) || (\result == false);
	//ensures (\forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
	//  spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) ) ==> 	(\result == false);
	//ensures !(\forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
	//  spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) ) ==> 	(\result == true);
@*/
static bool _geec_prime_smt_slab_getspatype_isiotbl(u32 slabid, u32 spa){
	u32 i;

	/*@
		loop invariant b1: 0 <= i <= MAX_PLATFORM_CPUS;
		loop invariant b2: \forall integer x; 0 <= x < i ==> (!(spa >= (u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
		  spa < ((u32)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) ));
		loop assigns i;
		loop variant MAX_PLATFORM_CPUS - i;
	@*/
	for(i=0; i < MAX_PLATFORM_CPUS; i++){
		if (spa >= (u32)&__xmhfhic_x86vmx_tss[i].tss_iobitmap &&
		  spa < ((u32)&__xmhfhic_x86vmx_tss[i].tss_iobitmap[3*PAGE_SIZE_4K]) ){
		    return true;
		}
	}

	return false;

}

#endif // 0







//TODO: we need to account for memgrant caps here
//memgrant is read-only or read-write
//for now we will return _SLAB_SPATYPE_SLAB_DATA for such
//shared mappings


#if 1
/*@
	requires 0 <= slab_index < XMHFGEEC_TOTAL_SLABS ;
	assigns \nothing;
	ensures ( (\result == _SLAB_SPATYPE_GEEC_PRIME_IOTBL) ||
		(\result == _SLAB_SPATYPE_SLAB_CODE) ||
		(\result == _SLAB_SPATYPE_SLAB_DATA) ||
		(\result == _SLAB_SPATYPE_SLAB_STACK) ||
		(\result == _SLAB_SPATYPE_SLAB_DMADATA) ||
		(\result == _SLAB_SPATYPE_SLAB_DEVICEMMIO) ||
		(\result == _SLAB_SPATYPE_OTHER) );
@*/
u32 gp_slab_getspatype_for_slab(u32 slab_index, u32 spa);
#endif // 0




//[DONE]
#if 1
//@ghost bool gisiotbl, gisdevicemmio;
/*@
	requires 0 <= slab_index < XMHFGEEC_TOTAL_SLABS ;
	requires \forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (_sda_slab_devicemap[slab_index].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
	requires 0 <= _sda_slab_devicemap[slab_index].device_count < MAX_PLATFORM_DEVICES;
	assigns gisiotbl, gisdevicemmio;
	ensures ( (\result == _SLAB_SPATYPE_GEEC_PRIME_IOTBL) ||
		(\result == _SLAB_SPATYPE_SLAB_CODE) ||
		(\result == _SLAB_SPATYPE_SLAB_DATA) ||
		(\result == _SLAB_SPATYPE_SLAB_STACK) ||
		(\result == _SLAB_SPATYPE_SLAB_DMADATA) ||
		(\result == _SLAB_SPATYPE_SLAB_DEVICEMMIO) ||
		(\result == _SLAB_SPATYPE_OTHER) );
	ensures ( (gisiotbl == true) ) ==> (\result == _SLAB_SPATYPE_GEEC_PRIME_IOTBL);
	ensures ( (gisiotbl == false) &&  (spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end)) ==> (\result == _SLAB_SPATYPE_SLAB_CODE);
	ensures ( (gisiotbl == false) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end) &&
		  (spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end)
		) ==> (\result == _SLAB_SPATYPE_SLAB_DATA);
	ensures ( (gisiotbl == false) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end) &&
		  (spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_end)
		) ==> (\result == _SLAB_SPATYPE_SLAB_STACK);
	ensures ( (gisiotbl == false) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_end) &&
		  (spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_end)
		) ==> (\result == _SLAB_SPATYPE_SLAB_DMADATA);
	ensures ( (gisiotbl == false) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_end) &&
		  (gisdevicemmio == true)
		) ==> (\result == _SLAB_SPATYPE_SLAB_DEVICEMMIO);


@*/
u32 gp_slab_getspatype_for_slab(u32 slab_index, u32 spa){
		bool isiotbl, isdevicemmio;

		isiotbl = _geec_prime_smt_slab_getspatype_isiotbl(slab_index, spa);
		//@ghost gisiotbl = isiotbl;
		isdevicemmio = _geec_prime_smt_slab_getspatype_isdevicemmio(slab_index, spa);
		//@ghost gisdevicemmio = isdevicemmio;

		if(isiotbl)
		    return _SLAB_SPATYPE_GEEC_PRIME_IOTBL;
		if(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end)
		    return _SLAB_SPATYPE_SLAB_CODE;
		if(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end)
		    return _SLAB_SPATYPE_SLAB_DATA;
		if(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_end)
		    return _SLAB_SPATYPE_SLAB_STACK;
		if(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_end)
		    return _SLAB_SPATYPE_SLAB_DMADATA;
		if(isdevicemmio)
		    return _SLAB_SPATYPE_SLAB_DEVICEMMIO;

		return _SLAB_SPATYPE_OTHER;
}
#endif // 0





#if 1
static u64 gp_uhslab_mempgtbl_getptflagsforspa_pae(u32 slabid, u32 spa, u32 spatype){
	u64 flags=0;
	u8 spa_slabtype, spa_slabregion;
	bool spa_sameslab=false;
	u32 slabtype = xmhfgeec_slab_info_table[slabid].slabtype;

	spa_slabregion = spatype & 0x0000000FUL;
	spa_slabtype =spatype & 0x000000F0UL;
	if(spatype & _SLAB_SPATYPE_MASK_SAMESLAB)
	spa_sameslab = true;


    switch(slabtype){
        case XMHFGEEC_SLABTYPE_uVT_PROG:
        case XMHFGEEC_SLABTYPE_uVU_PROG:{
            //self slab: code=rx, data,stack,dmadata,mmio=rw, perms=USER
            //other slab vft: code=rx, data,stack,dmadata,mmio=rw, perms=SUPER
            //SPATYPE_OTHER => rw perms=SUPER
            //anything else: mapped rw perms=SUPER
            if(spa_slabregion == _SLAB_SPATYPE_OTHER){
                flags = (u64)(_PAGE_PRESENT | _PAGE_RW);
            }else{
                if(spa_sameslab || spa_slabtype == XMHFGEEC_SLABTYPE_VfT_PROG ||
                    spa_slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL){
                    switch(spa_slabregion){
                        case _SLAB_SPATYPE_SLAB_CODE:
                            flags = (_PAGE_PRESENT);
                            break;
                        case _SLAB_SPATYPE_SLAB_DATA:
                        case _SLAB_SPATYPE_SLAB_STACK:
                        case _SLAB_SPATYPE_SLAB_DMADATA:
                        case _SLAB_SPATYPE_GEEC_PRIME_IOTBL:
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                            break;
                        case _SLAB_SPATYPE_SLAB_DEVICEMMIO:
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX | _PAGE_PCD);
                            break;
                        default:
                            flags = 0;
                            break;
                    }

                    if(spa_sameslab || spa_slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL)
                        flags |= (_PAGE_USER);

                }else{
                    flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                }

            }
        }
        break;

        default:
            //_XDPRINTF_("%s: invalid slab type=%x. Halting!\n", __func__, slabtype);
            //HALT();
            flags = 0;
            break;

    }

    return flags;
}

#endif // 0




#if 1
//[DONE]
static u64 gp_vhslab_mempgtl_getptflagsforspa_pae(u32 slabid, u32 spa, u32 spatype){
	u64 flags=0;


     if( xmhfgeec_slab_info_table[slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG){

            //self slab: code=rx, data,stack,dmadata,mmio=rw, perms=SUPER
            //other slab vft: code=rx, data,stack,dmadata,mmio=rw, perms=SUPER
            //SPATYPE_OTHER => rw perms=SUPER
            //anything else: mapped rw perms=SUPER
            if( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_OTHER){
                flags = (u64)(_PAGE_PRESENT | _PAGE_RW);
            }else{
                if( (spatype & _SLAB_SPATYPE_MASK_SAMESLAB) || (spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_PROG ||
                    (spatype & 0x000000F0UL) == XMHFGEEC_SLABTYPE_VfT_SENTINEL){
                    if( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_CODE)
                            flags = (_PAGE_PRESENT);
                    else if( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DATA ||
			     (spatype & 0x0000000FUL) ==  _SLAB_SPATYPE_SLAB_STACK ||
                             (spatype & 0x0000000FUL) ==  _SLAB_SPATYPE_SLAB_DMADATA ||
			     (spatype & 0x0000000FUL) ==  _SLAB_SPATYPE_GEEC_PRIME_IOTBL)
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
		    else if ( (spatype & 0x0000000FUL) == _SLAB_SPATYPE_SLAB_DEVICEMMIO)
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX | _PAGE_PCD);
                }else{
                    flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                }

            }

     }

    return flags;
}
#endif // 0


#if 1






//setup unverified hypervisor (uh) slab memory page tables
static void gp_setup_uhslab_mempgtbl(u32 slabid){
	u64 gpa;
	u64 flags;
	u32 spatype;
	u32 spa_slabregion, spa_slabtype;
	u32 slabtype = xmhfgeec_slab_info_table[slabid].slabtype;
	u32 uhslabmempgtbl_idx;
	u32 i, j;
	u64 default_flags = (u64)(_PAGE_PRESENT);

	if(!(slabid >= XMHFGEEC_UHSLAB_BASE_IDX && slabid <= XMHFGEEC_UHSLAB_MAX_IDX)){
		_XDPRINTF_("%s: slab %u --> Fatal error uV{T,U} slab out of UH slab idx bound!\n", __func__, i);
		HALT();
	}

	uhslabmempgtbl_idx = slabid - XMHFGEEC_UHSLAB_BASE_IDX;

	//pdpt
	memset(&gp_rwdatahdr.gp_uhslabmempgtbl_lvl4t[uhslabmempgtbl_idx], 0, PAGE_SIZE_4K);
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		gp_rwdatahdr.gp_uhslabmempgtbl_lvl4t[uhslabmempgtbl_idx][i] =
		    pae_make_pdpe(&gp_uhslabmempgtbl_lvl2t[uhslabmempgtbl_idx][i], default_flags);
	}

	//pdt
	default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			gp_uhslabmempgtbl_lvl2t[uhslabmempgtbl_idx][i][j] =
				pae_make_pde(&gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][i][j], default_flags);
		}
	}


	//pts
	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_4K){
		u64 pdpt_index = pae_get_pdpt_index(gpa);
		u64 pdt_index = pae_get_pdt_index(gpa);
		u64 pt_index = pae_get_pt_index(gpa);

		spatype =  gp_s2_setupmpgtbl_getspatype(slabid, (u32)gpa);
		spa_slabregion = spatype & 0x0000000FUL;
		spa_slabtype =spatype & 0x000000F0UL;
		flags = gp_uhslab_mempgtbl_getptflagsforspa_pae(slabid, (u32)gpa, spatype);

		//_XDPRINTF_("gpa=%08x, flags=%016llx\n", (u32)gpa, flags);

		if(spa_slabregion == _SLAB_SPATYPE_GEEC_PRIME_IOTBL &&
		   slabtype != XMHFGEEC_SLABTYPE_VfT_PROG && slabtype != XMHFGEEC_SLABTYPE_VfT_SENTINEL){
			//map unverified slab iotbl instead (12K)
			gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][pdpt_index][pdt_index][pt_index] =
				pae_make_pte(xmhfgeec_slab_info_table[slabid].iotbl_base, flags) & (~0x80);
			//_XDPRINTF_("slab %u: iotbl mapping, orig gpa=%08x, revised entry=%016llx\n", slabid,
			//           (u32)gpa, setentryforpaddrp->entry);

			gpa += PAGE_SIZE_4K;

			gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][pdpt_index][pdt_index][pt_index] =
				pae_make_pte(xmhfgeec_slab_info_table[slabid].iotbl_base+PAGE_SIZE_4K, flags) & (~0x80);
			//_XDPRINTF_("slab %u: iotbl mapping, orig gpa=%08x, revised entry=%016llx\n", slabid,
			//           (u32)gpa, setentryforpaddrp->entry);

			gpa += PAGE_SIZE_4K;

			gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][pdpt_index][pdt_index][pt_index] =
				pae_make_pte(xmhfgeec_slab_info_table[slabid].iotbl_base+(2*PAGE_SIZE_4K), flags) & (~0x80);
			//_XDPRINTF_("slab %u: iotbl mapping, orig gpa=%08x, revised entry=%016llx\n", slabid,
			//           (u32)gpa, setentryforpaddrp->entry);

			gpa += PAGE_SIZE_4K;
		}else{
			gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][pdpt_index][pdt_index][pt_index] =
				pae_make_pte(gpa, flags) & (~0x80);
		}
	}

}

#endif // 0


//@ghost u64 gflags[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];
/*@
	assigns gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[0..(PAGE_SIZE_4K-1)];
	assigns gp_vhslabmempgtbl_lvl2t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT)-1];
	assigns gp_vhslabmempgtbl_lvl1t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)-1];
	assigns gflags[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)-1];
	ensures (\forall u32 x; 0 <= x < PAE_PTRS_PER_PDPT ==>
		 ( ((u64)gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[x] ) == ( ((u64)(&gp_vhslabmempgtbl_lvl2t[x * PAE_PTRS_PER_PDT]) & 0x7FFFFFFFFFFFF000ULL ) | (u64)(_PAGE_PRESENT)) )
		);
	ensures (\forall u32 x; 0 <= x < PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT ==>
		 ( ( (u64)gp_vhslabmempgtbl_lvl2t[x] ) == ( ((u64)(&gp_vhslabmempgtbl_lvl1t[(x * PAE_PTRS_PER_PT)]) & 0x7FFFFFFFFFFFF000ULL ) | (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER))  )
		);
	ensures (\forall u32 x; 0 <= x < (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT) ==>
		 ( (u64)gp_vhslabmempgtbl_lvl1t[x] == ( ((u64)(x * PAGE_SIZE_4K) & 0x7FFFFFFFFFFFF000ULL ) | (u64)(gflags[x]) )   )
		);
@*/
static void gp_setup_vhslab_mempgtbl(void){
	u32 i;
	u64 flags=0;
	u32 spatype=0;
	u32 slabid = XMHFGEEC_SLAB_GEEC_PRIME;


	//pdpt setup
	memset(&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t, 0, PAGE_SIZE_4K);


    	/*@
		loop invariant a1: 0 <= i <= PAE_PTRS_PER_PDPT;
		loop invariant a2: \forall integer x; 0 <= x < i ==> ( (u64)gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[x] ) == ( ((u64)(&gp_vhslabmempgtbl_lvl2t[x * PAE_PTRS_PER_PDT]) & 0x7FFFFFFFFFFFF000ULL ) | ((u64)(_PAGE_PRESENT)));
		loop assigns gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[0..(PAE_PTRS_PER_PDPT-1)], i;
		loop variant PAE_PTRS_PER_PDPT - i;
	@*/
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[i] =
			pae_make_pdpe(&gp_vhslabmempgtbl_lvl2t[i * PAE_PTRS_PER_PDT], (u64)(_PAGE_PRESENT));
	}



	//pdt setup
    	/*@
		loop invariant a3: 0 <= i <= (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT);
		loop invariant a4: \forall integer x; 0 <= x < i ==> (( (u64)gp_vhslabmempgtbl_lvl2t[x] ) == ( ((u64)(&gp_vhslabmempgtbl_lvl1t[(x * PAE_PTRS_PER_PT)]) & 0x7FFFFFFFFFFFF000ULL ) | ((u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER))));
		loop assigns i, gp_vhslabmempgtbl_lvl2t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT)];
		loop variant (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT) - i;
	@*/
	for(i=0; i < PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT; i++){
			gp_vhslabmempgtbl_lvl2t[i] =
				pae_make_pde(&gp_vhslabmempgtbl_lvl1t[(i * PAE_PTRS_PER_PT)], (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER));
	}



	//pt setup
    	/*@	loop invariant a5: 0 <= i <= (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT);
		loop assigns gflags[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)], spatype, flags, i, gp_vhslabmempgtbl_lvl1t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)];
		loop invariant a6: \forall integer x; 0 <= x < i ==> ( (u64)gp_vhslabmempgtbl_lvl1t[x]) == ( ((u64)(x * PAGE_SIZE_4K) & 0x7FFFFFFFFFFFF000ULL ) | (u64)(gflags[x]) );
		loop variant (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT) - i;
	@*/
	for(i=0; i < (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT); ++i){
		spatype =  gp_s2_setupmpgtbl_getspatype(slabid, (u32)(i * PAGE_SIZE_4K));

		flags = gp_vhslab_mempgtl_getptflagsforspa_pae(slabid, (u32)(i * PAGE_SIZE_4K), spatype);
		//@ghost gflags[i] = flags;

		gp_vhslabmempgtbl_lvl1t[i] = pae_make_pte( (i*PAGE_SIZE_4K), flags);
	}



}


#if 1

void gp_s2_setupmempgtbl(void){
    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp =
        (xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *)spl.in_out_params;
    u32 i, slabtype;

    _XDPRINTF_("%s: starting...\n", __func__);

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid here



    //setup verified slabs' page tables, uses slab index for GEEC_PRIME
    //spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL;
    //initmempgtblp->dst_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    //XMHF_SLAB_CALLNEW(&spl);
    //_geec_prime_populate_slab_pagetables_pae4k(XMHFGEEC_SLAB_GEEC_PRIME);
    gp_setup_vhslab_mempgtbl();
   	_XDPRINTF_("%s: populated verified slabs' memory page tables\n", __func__);

    //setup unverified slabs's page tables
    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        slabtype = xmhfgeec_slab_info_table[i].slabtype;

        switch(slabtype){
            case XMHFGEEC_SLABTYPE_uVT_PROG:
            case XMHFGEEC_SLABTYPE_uVU_PROG:{
              	_XDPRINTF_("%s: slab %u --> ppopulating uV{T,U} page-tables...\n", __func__, i);
                gp_setup_uhslab_mempgtbl(i);
              	_XDPRINTF_("%s: slab %u --> uV{T,U}_prog page-tables populated\n", __func__, i);
            }
            break;


            case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
            case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
            case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
              	_XDPRINTF_("%s: slab %u --> ppopulating uV{T,U}_prog_guest page-tables...\n", __func__, i);
                spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL;
                initmempgtblp->dst_slabid = i;
                XMHF_SLAB_CALLNEW(&spl);
                gp_s2_setupmpgtblug(i);
              	_XDPRINTF_("%s: slab %u --> uV{T,U}_prog_guest page-tables populated\n", __func__, i);
            }
            break;

            default:
                break;
        }
    }


	_XDPRINTF_("%s: setup slab memory page tables\n", __func__);
    //_XDPRINTF_("%s: wip. halting!\n");
    //HALT();
}

#endif
