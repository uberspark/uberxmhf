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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

// svm_eap.c - SVM External Access Protection (a.k.a. DEV) implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

//initialize SVM EAP a.k.a DEV
//returns 1 if all went well, else 0
u32 svm_eap_initialize(void){
	u32 mc_capabilities_pointer;
	u32 mc_caplist_nextptr;
	u32 mc_caplist_id;
	u32 found_dev=0;
	
	u32 dev_hdr_reg=0;		//DEV header register (32-bit)
	u32 dev_fnidx_reg=0;	//DEV function/index register (32-bit)
	u32 dev_data_reg=0;		//DEV data register (32-bit)
	
	//we first need to detect the DEV capability block
	//the DEV capability block is in the PCI configuration space 
	//(15.24.4, AMD Dev. Vol2)
	//more precisely it is a part of the Miscellaneous Control	
	//HyperTransport Configuration space. (3.6, AMD BKDG)
	//HyperTransport device configuration space is 
 	//accessed by using bus 0, devices 24 to 31, where device 24 corresponds 
 	//to node 0 and device 31 corresponds to node 7. (2.11, AMD BKDG 10h family)
 	//note: node 0 corresponds to 0th physical CPU package. So, if we have
 	//four logical cores on the same physical die, the HT device is on
 	//bus 0 as device 24 for all the cores. well at least to my knowledge...
 	//Miscellaneous Control is function 3 (3.6, AMD BKDG)

	//step-1: we read capabilities pointer (PCI_CONF_HDR_IDX_CAPABILITIES_POINTER)
	//in b:d.f 0:24.3. If its 0, then DEV support is not available
		pci_type1_read(0, 24, 3, PCI_CONF_HDR_IDX_CAPABILITIES_POINTER, sizeof(u32), &mc_capabilities_pointer);
		if(mc_capabilities_pointer == 0)
			return 0;	//DEV support unavailable
	
		ASSERT ( (u8)(mc_capabilities_pointer) == 0xF0 ); //p. 286, AMD BKDG
	
	  //traverse the capabilities list as per the PCI spec.
	  mc_caplist_nextptr = (u32)(u8)mc_capabilities_pointer;
	  
	  do{
		  //get the ID of this capability block
		  pci_type1_read(0, 24, 3, mc_caplist_nextptr, sizeof(u8), &mc_caplist_id);
		  
			//check if this is a DEV capability ID block
			if((u8)mc_caplist_id == PCI_CAPABILITIES_POINTER_ID_DEV){
				found_dev = 1;
				break;
			}
		  
		  //get the index of the next capability block
			pci_type1_read(0, 24, 3, mc_caplist_nextptr, sizeof(u8), &mc_caplist_nextptr);
		}while(mc_caplist_nextptr != 0);
	

  	//did we find a DEV capability block above? if no simply return
  	if(!found_dev)
  		return 0;
  		
  	//okay, we found a DEV capability block at index mc_caplist_nextptr
		printf("\n%s: found DEV capability block at index %04x", __FUNCTION__, mc_caplist_nextptr);
		
		//now obtain the PCI configuration space indices for DEV header, fn/idx
		//and data registers
		dev_hdr_reg = mc_caplist_nextptr;
		dev_fnidx_reg = dev_hdr_reg + sizeof(u32);
		dev_data_reg = dev_hdr_reg + (2 * sizeof(u32));
		
		
		//print it out for now...
		printf("\n%s: dev_hdr_reg at %02x:%02x.%1x(%04x)", __FUNCTION__, 0, 24, 3, dev_hdr_reg);
		printf("\n%s: dev_fnidx_reg at %02x:%02x.%1x(%04x)", __FUNCTION__, 0, 24, 3, dev_fnidx_reg);
		printf("\n%s: dev_data_reg at %02x:%02x.%1x(%04x)", __FUNCTION__, 0, 24, 3, dev_data_reg);
		
		return 1;  	
}

