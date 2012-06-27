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

//	pci.c - peripheral component interconnect (PCI) interface implementation
//  author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

/*
	note on the two different types of PCI config space access methods
	(unfortunately only a fraction of this is in the PCI specs...
		maybe that is why the specs. are not public :p)
	
	type-1 accesses:
	
	this method uses two standard PCI I/O ports to initiate a 
	configuration cycle. The type of cycle is determined by the 
	host-bridge device based on the devices primary bus number. 
	if the configuration bus number matches the primary bus number then a 
	type 0 configuration cycle occurs. otherwise a type 1 cycle is generated. 
	this is all transparent to the user. more on type 0 and type 1 cycles 
	later...
	
	the two ports used for type-1 accesses are the  
	PCI_CONFIG_ADDR_PORT (0xCF8) and PCI_CONFIG_DATA_PORT (0xCFC).
	
	CF8h, 32-bit, r/w
	bits  0-7  	PCI conf. space index to read/write at CFCh
    		8-15  device and function
    		16-23 bus
  			24-27	extended 4-bits of PCI conf. space index for PCIe conf. space accesses 
	     	31  	set to enable the PCI bus configuration space

	CFCh, 32-bit, r/w
	bits  0-31  the PCI conf. space index specified in CF8h
           		can be accessed here for reads and writes.


	type-2 accesses:
	
	this method uses three standard PCI I/O ports to initiate a
	configuration cycle.
	
	the three ports used for type-2 accesses are the 
	PCI_CONFIG_ADDR_PORT (0xCF8), PCI_CONFIG_FORWARD_PORT (0xCFA), and 
	PCI_CONFIG_BASE_PORT (0xC000). 

	CF8h, 8-bit, r/w
	bits	0			reserved and set to 0
				1-3		3-bit function
				4-7		reserved all set to 1s
				
	CFAh, 8-bit, r/w
	bits	0-7 	8-bit bus
				
	the function and bus are sent out to PCI_CONFIG_ADDR_PORT and
	PCI_CONFIG_FORWARD_PORT respectively as above, this is followed
	by a read or write to the i/o port that is constructed as follows:
	
	32-bit i/o port to read/write required PCI conf. space index (reg) for device (dev)
	= (PCI_CONFIG_BASE_PORT | (dev << 8) | reg)

	Note that type-1 accesses can address 256bytes (regular PCI) or 
	4096bytes (PCIe) of PCI conf.	space. However, type-2 is limited to only
	256bytes.
	
	The mechanism supported (type-1 or type-2) depends on the PCI chipset
	implementation. All systems manufactured after 2001 seem to support 
	type-1 (ref: Linux Kernel), so we detect if it supports type-1 and go
	with that, else halt!
	
	Some info on PCI configuration cycles (thankfully
	this is in the PCI spec. :p)
	
	Type 0 PCI Configuration cycles do not contain a bus number and these 
	are interpreted by all devices as being for PCI configuration addresses on 
	this PCI bus. Bits 31:11 of the Type 0 configuraration cycles are treated as 
	the device select field. 
	
	Type 1 PCI Configuration cycles contain a PCI bus number and this type of 
	configuration cycle is ignored by all PCI devices except the PCI-PCI bridges. 
	All of the PCI-PCI Bridges seeing Type 1 configuration cycles may choose to 
	pass them to the PCI buses downstream of themselves. Whether the PCI-PCI 
	Bridge ignores the Type 1 configuration cycle or passes it onto the downstream 
	PCI bus depends on how the PCI-PCI Bridge has been configured. Every 
	PCI-PCI bridge has a primary bus interface number and a secondary bus 
	interface number. The primary bus interface being the one nearest the CPU 
	and the secondary bus interface being the one furthest away. 
	Each PCI-PCI Bridge also has a subordinate bus number and this is the 
	maximum bus number of all the PCI buses that are bridged beyond the 
	secondary bus interface. Or to put it another way, the subordinate bus 
	number is the highest numbered PCI bus downstream of the PCI-PCI bridge. 
	
	When the PCI-PCI bridge sees a Type 1 PCI configuration cycle it does one of 
	the following things:

  *Ignore it if the bus number specified is not in between the bridge's 
  secondary bus number and subordinate bus number (inclusive),

  *Convert it to a Type 0 configuration command if the bus number specified 
  matches the secondary bus number of the bridge,

  *Pass it onto the secondary bus interface unchanged if the bus number 
  specified is greater than the secondary bus number and less than or equal 
	to the subordinate bus number	
	
	geronimo...
*/

//==============================================================================
//static (local) functions
//==============================================================================

//enumerates the PCI bus on the system
static void _pci_enumeratebus(void){
	u32 b, d, f;

	//bus numbers range from 0-255, device from 0-31 and function from 0-7	
	for(b=0; b < PCI_BUS_MAX; b++){
		for(d=0; d < PCI_DEVICE_MAX; d++){
			for(f=0; f < PCI_FUNCTION_MAX; f++){		
				u32 vendor_id, device_id;
				//read device and vendor ids, if no device then both will be 0xFFFF
				emhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_VENDOR_ID, sizeof(u16), &vendor_id);
				emhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_DEVICE_ID, sizeof(u16), &device_id);
				if(vendor_id == 0xFFFF && device_id == 0xFFFF)
					break;
				
				printf("\n	%02x:%02x.%1x -> vendor_id=%04x, device_id=%04x", b, d, f, vendor_id, device_id);						
			}
		}
	}

  	
}


//does a PCI type-1 read of PCI config space for a given bus, device, 
//function and index
//len = 1(byte), 2(word) and 4(dword)
//value is a pointer to a 32-bit dword which contains the value read
void emhf_baseplatform_arch_x86_pci_type1_read(u32 bus, u32 device, u32 function, u32 index, u32 len,
			u32 *value){
        
	//sanity checks
	ASSERT( bus <= 255 );
  ASSERT( PCI_DEVICE_FN(device,function) <= 255 );
  ASSERT( index <= 4095 );
  
  //encode and send the 32-bit type-1 address to PCI address port
	outl(PCI_TYPE1_ADDRESS(bus, device, function, index), PCI_CONFIG_ADDR_PORT);

  //read a byte, word or dword depending on len
  switch (len) {
  	case 1:	//byte
          *value = inb(PCI_CONFIG_DATA_PORT + (index & 3));
          break;
  	case 2:	//word
          *value = inw(PCI_CONFIG_DATA_PORT + (index & 2));
          break;
  	case 4:	//dword
          *value = inl(PCI_CONFIG_DATA_PORT);
          break;
  }

	return;
}

//does a PCI type-1 write of PCI config space for a given bus, device, 
//function and index
//len = 1(byte), 2(word) and 4(dword)
//value contains the value to be written

void emhf_baseplatform_arch_x86_pci_type1_write(u32 bus, u32 device, u32 function, u32 index, u32 len,
	u32 value){

 	//sanity checks
	ASSERT( bus <= 255 );
  ASSERT( PCI_DEVICE_FN(device,function) <= 255 );
  ASSERT( index <= 4095 );

  //encode and send the 32-bit type-1 address to PCI address port
	outl(PCI_TYPE1_ADDRESS(bus, device, function, index), PCI_CONFIG_ADDR_PORT);

  //write a byte, word or dword depending on len
	switch (len) {
  	case 1:	//byte
      outb((u8)value, PCI_CONFIG_DATA_PORT + (index & 3));
      break;
    
		case 2:	//word
      outw((u16)value, PCI_CONFIG_DATA_PORT + (index & 2));
      break;
  
	  case 4:	//dword
      outl((u32)value, PCI_CONFIG_DATA_PORT);
      break;
  }

  return;
}

//PCI subsystem initialization
//check that PCI chipset supports type-1 accesses
//true for most systems after 2001
void emhf_baseplatform_arch_x86_pci_initialize(void){
  u32 tmp;

	//save value at PCI_CONFIG_ADDR_PORT
  tmp = inl(PCI_CONFIG_ADDR_PORT);
  
  //select command register on bus 0, device 0 and function 0
  outl(0x80000000, PCI_CONFIG_ADDR_PORT);
  
  //reading PCI_CONFIG_ADDR_PORT should return with bit 31 set
	//if system supports type-1 access
  if (inl(PCI_CONFIG_ADDR_PORT) != 0x80000000) {
  	printf("\n%s: system does not support type-1 access. HALT!", __FUNCTION__);
		HALT();	
  }

  //restore previous value at PCI_CONFIG_ADDR_PORT
  outl(tmp, PCI_CONFIG_ADDR_PORT);

	//say we are good to go and enumerate the PCI bus 
	printf("\n%s: PCI type-1 access supported.", __FUNCTION__);
	printf("\n%s: PCI bus enumeration follows:", __FUNCTION__);
	_pci_enumeratebus();
	printf("\n%s: Done with PCI bus enumeration.", __FUNCTION__);

	return;
}
				
