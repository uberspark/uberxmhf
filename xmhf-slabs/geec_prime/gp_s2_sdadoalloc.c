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


void gp_s2_sdadoalloc(void){
	u32 i;
	u32 dst_slabid;

        for(i=0; i <numentries_sysdev_memioregions; i++){
            if(sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
               sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
               sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN){

		dst_slabid = gp_s2_sdadoalloc_getuobjfordev(sysdev_memioregions[i].b,
							sysdev_memioregions[i].d,
							sysdev_memioregions[i].f);
                if(dst_slabid == 0xFFFFFFFFUL){
                    _XDPRINTF_("Could not find slab for device %x:%x:%x (vid:did=%x:%x, type=%x), skipping...\n", sysdev_memioregions[i].b,
                               sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                               sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype);
                }else{
			gp_s2_sdabinddevice(dst_slabid, vtd_pagewalk_level,
						sysdev_memioregions[i].b, sysdev_memioregions[i].d, sysdev_memioregions[i].f);

                    _XDPRINTF_("Allocated device %x:%x:%x (vid:did=%x:%x, type=%x) to slab %u...\n", sysdev_memioregions[i].b,
                               sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                               sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype, dst_slabid);
                }
            }
        }
}

