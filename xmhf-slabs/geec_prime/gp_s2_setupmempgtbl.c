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






//////////////////////////////////////////////////////////////////////////////
// setup slab memory page tables (smt)

#define _SLAB_SPATYPE_MASK_SAMESLAB             (0x100)

#define	_SLAB_SPATYPE_SLAB_CODE					(0x0)
#define	_SLAB_SPATYPE_SLAB_DATA	    			(0x1)
#define _SLAB_SPATYPE_SLAB_STACK				(0x2)
#define _SLAB_SPATYPE_SLAB_DMADATA				(0x3)
#define _SLAB_SPATYPE_SLAB_DEVICEMMIO           (0x4)
#define _SLAB_SPATYPE_GEEC_PRIME_IOTBL          (0x5)

#define _SLAB_SPATYPE_OTHER	    				(0x6)

/*@
  //requires n >= 0;
	assigns \nothing;
	ensures 0 <= \result < PAGE_SIZE_4K;
@*/
static u64 _geec_prime_slab_getptflagsforspa_pae(u32 slabid, u32 spa, u32 spatype);



#if 0

static bool _geec_prime_smt_slab_getspatype_isdevicemmio(u32 slabid, u32 spa){
    u32 i, j;

    for(i=0; i < _sda_slab_devicemap[slabid].device_count; i++){
        u32 sysdev_memioregions_index = _sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i];
        for(j=0; j < PCI_CONF_MAX_BARS; j++){
            if(sysdev_memioregions[sysdev_memioregions_index].memioextents[j].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM){
                if(spa >= sysdev_memioregions[sysdev_memioregions_index].memioextents[j].addr_start &&
                    spa < sysdev_memioregions[sysdev_memioregions_index].memioextents[j].addr_end)
                    return true;
            }
        }
    }

    return false;
}

#endif // 0



/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	assigns \nothing;
	//behavior spa_iotbl:

	//behavior spa_notiotbl:

	//complete behaviours;
	//disjoint behaviors;
@*/
static bool _geec_prime_smt_slab_getspatype_isiotbl(u32 slabid, u32 spa){
    u32 i;

	/*@
		loop invariant b1: 0 <= i <= MAX_PLATFORM_CPUS;
		loop assigns i;
		loop variant MAX_PLATFORM_CPUS - i;
	@*/
    for(i=0; i < MAX_PLATFORM_CPUS; i++){
      if (spa >= (u32)&__xmhfhic_x86vmx_tss[i].tss_iobitmap &&
          spa < ((u32)&__xmhfhic_x86vmx_tss[i].tss_iobitmap[3*PAGE_SIZE_4K]) )
            return true;
    }

    return false;
}


#if 0

//TODO: we need to account for memgrant caps here
//memgrant is read-only or read-write
//for now we will return _SLAB_SPATYPE_SLAB_DATA for such
//shared mappings
static u32 _geec_prime_slab_getspatype(u32 slab_index, u32 spa){
	u32 i;




	//slab memory regions
	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		u32 mask = xmhfgeec_slab_info_table[i].slabtype;
		bool slab_rwcaps =
			(xmhfgeec_slab_info_table[i].slab_memgrantreadcaps & XMHFGEEC_SLAB_MEMGRANTREADCAP_MASK(slab_index)) ||
			(xmhfgeec_slab_info_table[i].slab_memgrantwritecaps & XMHFGEEC_SLAB_MEMGRANTWRITECAP_MASK(slab_index));


        if( i == slab_index || slab_rwcaps)
            mask |= _SLAB_SPATYPE_MASK_SAMESLAB;

        if(_geec_prime_smt_slab_getspatype_isiotbl(slab_index, spa))
            return _SLAB_SPATYPE_GEEC_PRIME_IOTBL | mask;
        if(spa >= xmhfgeec_slab_info_table[i].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[i].slab_physmem_extents[0].addr_end)
            return _SLAB_SPATYPE_SLAB_CODE | mask;
        if(spa >= xmhfgeec_slab_info_table[i].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[i].slab_physmem_extents[1].addr_end)
            return _SLAB_SPATYPE_SLAB_DATA | mask;
        if(spa >= xmhfgeec_slab_info_table[i].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[i].slab_physmem_extents[2].addr_end)
            return _SLAB_SPATYPE_SLAB_STACK | mask;
        if(spa >= xmhfgeec_slab_info_table[i].slab_physmem_extents[3].addr_start && spa < xmhfgeec_slab_info_table[i].slab_physmem_extents[3].addr_end)
            return _SLAB_SPATYPE_SLAB_DMADATA | mask;
        if(_geec_prime_smt_slab_getspatype_isdevicemmio(slab_index, spa))
            return _SLAB_SPATYPE_SLAB_DEVICEMMIO | mask;

	}

	return _SLAB_SPATYPE_OTHER;
}



// for VfT_PROG, uVT_PROG and uVU_PROG
static u64 _geec_prime_slab_getptflagsforspa_pae(u32 slabid, u32 spa, u32 spatype){
	u64 flags=0;
    u8 spa_slabtype, spa_slabregion;
    bool spa_sameslab=false;
	//_XDPRINTF_("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __func__, slab_index, spa, spatype);
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



        case XMHFGEEC_SLABTYPE_VfT_PROG:{
            //self slab: code=rx, data,stack,dmadata,mmio=rw, perms=SUPER
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

                }else{
                    flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                }

            }

        }
        break;

        default:
            _XDPRINTF_("%s: invalid slab type=%x. Halting!\n", __func__,
                       slabtype);
            HALT();

    }

    return flags;
}




// only for uVU_PROG_GUEST, uVU_PROG_RICHGUEST and uVT_PROG_GUEST
static u64 _geec_prime_slab_getptflagsforspa_ept(u32 slabid, u32 spa, u32 spatype){
	u64 flags=0;
    u8 spa_slabtype, spa_slabregion;
    bool spa_sameslab=false;
	//_XDPRINTF_("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __func__, slab_index, spa, spatype);
    u32 slabtype = xmhfgeec_slab_info_table[slabid].slabtype;

    spa_slabregion = spatype & 0x0000000FUL;
    spa_slabtype =spatype & 0x000000F0UL;
    if(spatype & _SLAB_SPATYPE_MASK_SAMESLAB)
        spa_sameslab = true;


    switch(slabtype){

        case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:{
            //code=rx, data,stack,dmadata,mmio=rw;
            //other slabs = no mapping; other region = no mapping
            if(spa_sameslab && spa_slabregion != _SLAB_SPATYPE_OTHER){
                switch(spa_slabregion){
                    case _SLAB_SPATYPE_SLAB_CODE:
                        flags = 0x5;
                        break;
                    case _SLAB_SPATYPE_SLAB_DATA:
                    case _SLAB_SPATYPE_SLAB_STACK:
                    case _SLAB_SPATYPE_SLAB_DMADATA:
                    case _SLAB_SPATYPE_SLAB_DEVICEMMIO:
                        flags = 0x3;
                        break;
                    default:
                        flags = 0;
                        break;
                }
            }else{
                flags=0;
            }
        }
        break;

        case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
            //code,data,stack,dmadata,mmio=rwx;
            //other slabs = no mapping; other region = no mapping
            if(spa_sameslab && spa_slabregion != _SLAB_SPATYPE_GEEC_PRIME_IOTBL)
                flags = 0x7;
            else
                flags = 0;
        }
        break;

        default:
            _XDPRINTF_("%s: invalid slab type=%x. Halting!\n", __func__,
                       slabtype);
            HALT();
    }

    return flags;

}

//---get memory type for a given physical page address--------------------------
//
//11.11.4.1 MTRR Precedences
//  0. if MTRRs are not enabled --> MTRR_TYPE_UC
//  if enabled then
     //if physaddr < 1MB use fixed MTRR ranges return type
     //else if within a valid variable range MTRR then
        //if a single match, return type
        //if two or more and one is UC, return UC
        //if two or more and WB and WT, return WT
        //else invalid combination
     //else
       // return default memory type
//
static u32 _geec_prime_vmx_getmemorytypeforphysicalpage(u64 pagebaseaddr){
 int i;
 u32 prev_type= MTRR_TYPE_RESV;

  //check if page base address under 1M, if so used FIXED MTRRs
  if(pagebaseaddr < (1024*1024)){
    for(i=0; i < MAX_FIXED_MEMORYTYPE_ENTRIES; i++){
      if( pagebaseaddr >= _vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= _vmx_ept_memorytypes[i].endaddr )
        return _vmx_ept_memorytypes[i].type;
    }

    _XDPRINTF_("\n%s: endaddr < 1M and unmatched fixed MTRR. Halt!", __func__);
    HALT();
  }

  //page base address is above 1M, use VARIABLE MTRRs
  for(i= MAX_FIXED_MEMORYTYPE_ENTRIES; i < MAX_MEMORYTYPE_ENTRIES; i++){
    if( pagebaseaddr >= _vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= _vmx_ept_memorytypes[i].endaddr &&
          (!_vmx_ept_memorytypes[i].invalid) ){
       if(_vmx_ept_memorytypes[i].type == MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_UC;
       }else if(_vmx_ept_memorytypes[i].type == MTRR_TYPE_WT && prev_type != MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_WT;
       }else{
        if(prev_type != MTRR_TYPE_UC && prev_type != MTRR_TYPE_WT){
          if(prev_type == MTRR_TYPE_RESV){
            prev_type = _vmx_ept_memorytypes[i].type;
          }else{
            _XDPRINTF_("\nprev_type=%u, _vmx_ept_memorytypes=%u", prev_type, _vmx_ept_memorytypes[i].type);
            HALT_ON_ERRORCOND ( prev_type == _vmx_ept_memorytypes[i].type);
          }
        }
       }
    }
  }

  if(prev_type == MTRR_TYPE_RESV)
    prev_type = MTRR_TYPE_WB; //todo: need to dynamically get the default MTRR (usually WB)

  return prev_type;
}




//setup unverified guest (ug) slab memory page tables
static void gp_setup_ugslab_mempgtbl(u32 slabid){
	u64 p_table_value;
	u64 gpa;
	u64 flags;
	u32 spatype;
	slab_params_t spl;
	xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
	(xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;

	spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
	spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid

	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_4K){
		u32 memorytype = _geec_prime_vmx_getmemorytypeforphysicalpage((u64)gpa);
		spatype = _geec_prime_slab_getspatype(slabid, (u32)gpa);
		flags = _geec_prime_slab_getptflagsforspa_ept(slabid, (u32)gpa, spatype);

		if(memorytype == 0)
		    p_table_value = (u64) (gpa)  | ((u64)memorytype << 3) |  flags ;	//present, UC
		else
		    p_table_value = (u64) (gpa)  | ((u64)6 << 3) | flags ;	//present, WB, track host MTRR

		spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
		setentryforpaddrp->dst_slabid = slabid;
		setentryforpaddrp->gpa = gpa;
		setentryforpaddrp->entry = p_table_value;
		XMHF_SLAB_CALLNEW(&spl);
	}
}



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

		spatype =  _geec_prime_slab_getspatype(slabid, (u32)gpa);
		spa_slabregion = spatype & 0x0000000FUL;
		spa_slabtype =spatype & 0x000000F0UL;
		flags = _geec_prime_slab_getptflagsforspa_pae(slabid, (u32)gpa, spatype);

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




#if 0
/*@
	assigns gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[0..(PAGE_SIZE_4K-1)];

@*/
static void gp_setup_vhslab_mempgtbl(void){
	u32 i, j;
	u64 default_flags = (u64)(_PAGE_PRESENT);

	u64 gpa;
	u64 flags=0;
	u32 spatype;
	u32 spa_slabregion, spa_slabtype;
	u32 slabid = XMHFGEEC_SLAB_GEEC_PRIME;
	u32 slabtype = xmhfgeec_slab_info_table[slabid].slabtype;


	//@assert (0x123FFA546ULL & 0xFFFFF000ULL) == 0x23FFA000ULL;
	//pdpt
	memset(&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t, 0, PAGE_SIZE_4K);

    	/*@
		loop invariant a1: 0 <= i <= PAE_PTRS_PER_PDPT;
		loop invariant a2: \forall integer x; 0 <= x < i ==> ( (u64)gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[x] ) == ( ((u64)(&gp_vhslabmempgtbl_lvl2t[x * PAE_PTRS_PER_PDT]) & 0x7FFFFFFFFFFFF000ULL ) | ((u64)(_PAGE_PRESENT)));
		loop assigns gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[0..(PAE_PTRS_PER_PDPT-1)], i;
		loop variant PAE_PTRS_PER_PDPT - i;
	@*/
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[i] =
			pae_make_pdpe(&gp_vhslabmempgtbl_lvl2t[i * PAE_PTRS_PER_PDT], default_flags);

		// //@assert ( (u64)gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[i] ) == ( ((u64)(&gp_vhslabmempgtbl_lvl2t[i]) & 0x7FFFFFFFFFFFF000ULL ) | (u64)(default_flags));
	}


	//pdt
	default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
    	/*@
		loop invariant a3: 0 <= i <= (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT);
		loop invariant a4: \forall integer x; 0 <= x < i ==> (( (u64)gp_vhslabmempgtbl_lvl2t[x] ) == ( ((u64)(&gp_vhslabmempgtbl_lvl1t[(x * PAE_PTRS_PER_PT)]) & 0x7FFFFFFFFFFFF000ULL ) | ((u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER))));
		loop assigns i, gp_vhslabmempgtbl_lvl2t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT)];
		loop variant (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT) - i;
	@*/
	for(i=0; i < PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT; i++){
			gp_vhslabmempgtbl_lvl2t[i] =
				pae_make_pde(&gp_vhslabmempgtbl_lvl1t[(i * PAE_PTRS_PER_PT)], default_flags);

			// //@assert ( (u64)gp_vhslabmempgtbl_lvl2t[i] ) == ( ((u64)(&gp_vhslabmempgtbl_lvl1t[(i * PAE_PTRS_PER_PT)]) & 0x7FFFFFFFFFFFF000ULL ) | (u64)(default_flags));
	}



	//pts
	//@ ghost u64 shadow_gp_vhslabmempgtbl_lvl1t[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];
    	/*@	loop invariant a5: 0 <= i <= (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT);
		loop assigns shadow_gp_vhslabmempgtbl_lvl1t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)], spatype, flags, i, gp_vhslabmempgtbl_lvl1t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)];
		loop invariant a6: \forall integer x; 0 <= x < i ==> ( (u64)shadow_gp_vhslabmempgtbl_lvl1t[x] == (u64)(x * PAGE_SIZE_4K) );
		loop variant (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT) - i;
	@*/
	for(i=0; i < (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT); ++i){
		spatype =  _geec_prime_slab_getspatype(slabid, (u32)(i * PAGE_SIZE_4K));
		flags = _geec_prime_slab_getptflagsforspa_pae(slabid, (u32)(i * PAGE_SIZE_4K), spatype);

		//@assert 0 <= flags < PAGE_SIZE_4K;
		gp_vhslabmempgtbl_lvl1t[i] = pae_make_pte( (i*PAGE_SIZE_4K), flags);
		//@ ghost shadow_gp_vhslabmempgtbl_lvl1t[i] = (i*PAGE_SIZE_4K);

		//@assert (u64)gp_vhslabmempgtbl_lvl1t[i] == ( ((u64)(i * PAGE_SIZE_4K) & 0x7FFFFFFFFFFFF000ULL ) | (u64)(flags) );
	}


}



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
                gp_setup_ugslab_mempgtbl(i);
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
