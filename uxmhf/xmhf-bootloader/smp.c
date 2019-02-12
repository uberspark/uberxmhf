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

//------------------------------------------------------------------------------
//smp.c
//this module scans for multi-core/CPUs within the system and
//returns the number of cores/CPUs as well as their LAPIC id,
//version, base and BSP indications
//author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>



//forward prototypes
static int mp_checksum(unsigned char *mp, int len);
static uint32_t mp_scan_config(uint32_t base, uint32_t length, MPFP **mpfp);
static uint32_t mp_getebda(void);
ACPI_RSDP * ACPIGetRSDP(void);

//exposed interface to the outside world
//inputs: array of type PCPU and pointer to uint32_t which will
//receive the number of cores/CPUs in the system
//returns: 1 on succes, 0 on any failure
uint32_t smp_getinfo(PCPU *pcpus, uint32_t *num_pcpus){
	MPFP *mpfp;
	MPCONFTABLE *mpctable;

	ACPI_RSDP *rsdp;

#if 0
	ACPI_XSDT *xsdt;
	uint32_t n_xsdt_entries;
	uint64_t *xsdtentrylist;
#else
	ACPI_RSDT	*rsdt;
	uint32_t n_rsdt_entries;
	uint32_t *rsdtentrylist;
#endif

  ACPI_MADT *madt;
	uint8_t madt_found=0;
	uint32_t i;

	//we scan ACPI MADT and then the MP configuration table if one is
	//present, in that order!

	//if we get here it means that we did not find a MP table, so
	//we need to look at ACPI MADT. Logical cores on some machines
	//(e.g HP8540p laptop with Core i5) are reported only using ACPI MADT
	//and there is no MP structures on such systems!
	_XDPRINTF_("\nFinding SMP info. via ACPI...");
	rsdp=(ACPI_RSDP *)ACPIGetRSDP();
	if(!rsdp){
		_XDPRINTF_("\nSystem is not ACPI Compliant, falling through...");
		goto fallthrough;
	}

	_XDPRINTF_("\nACPI RSDP at 0x%08x", (uint32_t)rsdp);

#if 0
	xsdt=(ACPI_XSDT *)(uint32_t)rsdp->xsdtaddress;
	n_xsdt_entries=(uint32_t)((xsdt->length-sizeof(ACPI_XSDT))/8);

	_XDPRINTF_("\nACPI XSDT at 0x%08x", xsdt);
  _XDPRINTF_("\n	len=0x%08x, headerlen=0x%08x, numentries=%u",
			xsdt->length, sizeof(ACPI_XSDT), n_xsdt_entries);

  xsdtentrylist=(uint64_t *) ( (uint32_t)xsdt + sizeof(ACPI_XSDT) );

	for(i=0; i< n_xsdt_entries; i++){
    madt=(ACPI_MADT *)( (uint32_t)xsdtentrylist[i]);
    if(madt->signature == ACPI_MADT_SIGNATURE){
    	madt_found=1;
    	break;
    }
	}
#else
	rsdt=(ACPI_RSDT *)(uint32_t)rsdp->rsdtaddress;
	n_rsdt_entries=(uint32_t)((rsdt->length-sizeof(ACPI_RSDT))/4);

	_XDPRINTF_("\nACPI RSDT at 0x%08x", (uint32_t)rsdt);
  _XDPRINTF_("\n	len=0x%08x, headerlen=0x%08x, numentries=%u",
			rsdt->length, sizeof(ACPI_RSDT), n_rsdt_entries);

  rsdtentrylist=(uint32_t *) ( (uint32_t)rsdt + sizeof(ACPI_RSDT) );

	for(i=0; i< n_rsdt_entries; i++){
    madt=(ACPI_MADT *)( (uint32_t)rsdtentrylist[i]);
    if(madt->signature == ACPI_MADT_SIGNATURE){
    	madt_found=1;
    	break;
    }
	}

#endif


	if(!madt_found){
		_XDPRINTF_("\nACPI MADT not found, falling through...");
		goto fallthrough;
	}

	_XDPRINTF_("\nACPI MADT at 0x%08x", (uint32_t)madt);
	_XDPRINTF_("\n	len=0x%08x, record-length=%u bytes", madt->length,
			madt->length - sizeof(ACPI_MADT));

	//scan through MADT APIC records to find processors
	*num_pcpus=0;
	{
		uint32_t madtrecordlength = madt->length - sizeof(ACPI_MADT);
		uint32_t madtcurrentrecordoffset=0;
		uint32_t i=0;
		uint32_t foundcores=0;

		do{
			ACPI_MADT_APIC *apicrecord = (ACPI_MADT_APIC *)((uint32_t)madt + sizeof(ACPI_MADT) + madtcurrentrecordoffset);
 		  _XDPRINTF_("\nrec type=0x%02x, length=%u bytes, flags=0x%08x, id=0x%02x", apicrecord->type,
			 		apicrecord->length, apicrecord->flags, apicrecord->lapicid);

			if(apicrecord->type == 0x0 && (apicrecord->flags & 0x1)){ //processor record

		    foundcores=1;
				HALT_ON_ERRORCOND( *num_pcpus < MAX_PCPU_ENTRIES);
				i = *num_pcpus;
				pcpus[i].lapic_id = apicrecord->lapicid;
		    pcpus[i].lapic_ver = 0;
		    pcpus[i].lapic_base = madt->lapicaddress;
		    if(i == 0)
					pcpus[i].isbsp = 1;	//ACPI spec says that first processor entry MUST be BSP
				else
					pcpus[i].isbsp = 0;

				*num_pcpus = *num_pcpus + 1;
			}
			madtcurrentrecordoffset += apicrecord->length;
		}while(madtcurrentrecordoffset < madtrecordlength);

		if(foundcores)
			return 1;
	}


fallthrough:
	//ok, ACPI detection failed proceed with MP table scan
	//we simply grab all the info from there as per
	//the intel MP spec.
	//look at 1K at start of conventional mem.
	//look at 1K at top of conventional mem
	//look at 1K starting at EBDA and
	//look at 64K starting at 0xF0000

	if( mp_scan_config(0x0, 0x400, &mpfp) ||
			mp_scan_config(639 * 0x400, 0x400, &mpfp) ||
			mp_scan_config(mp_getebda(), 0x400, &mpfp) ||
			mp_scan_config(0xF0000, 0x10000, &mpfp) ){

	    _XDPRINTF_("\nMP table found at: 0x%08x", (uint32_t)mpfp);
  		_XDPRINTF_("\nMP spec rev=0x%02x", mpfp->spec_rev);
  		_XDPRINTF_("\nMP feature info1=0x%02x", mpfp->mpfeatureinfo1);
  		_XDPRINTF_("\nMP feature info2=0x%02x", mpfp->mpfeatureinfo2);
  		_XDPRINTF_("\nMP Configuration table at 0x%08x", mpfp->paddrpointer);

  		HALT_ON_ERRORCOND( mpfp->paddrpointer != 0 );
			mpctable = (MPCONFTABLE *)mpfp->paddrpointer;
  		HALT_ON_ERRORCOND(mpctable->signature == MPCONFTABLE_SIGNATURE);

		  {//debug
		    int i;
		    _XDPRINTF_("\nOEM ID: ");
		    for(i=0; i < 8; i++)
		      _XDPRINTF_("%c", mpctable->oemid[i]);
		    _XDPRINTF_("\nProduct ID: ");
		    for(i=0; i < 12; i++)
		      _XDPRINTF_("%c", mpctable->productid[i]);
		  }

		  _XDPRINTF_("\nEntry count=%u", mpctable->entrycount);
		  _XDPRINTF_("\nLAPIC base=0x%08x", mpctable->lapicaddr);

		  //now step through CPU entries in the MP-table to determine
		  //how many CPUs we have
		  *num_pcpus=0;

			{
		    int i;
		    uint32_t addrofnextentry= (uint32_t)mpctable + sizeof(MPCONFTABLE);

		    for(i=0; i < mpctable->entrycount; i++){
		      MPENTRYCPU *cpu = (MPENTRYCPU *)addrofnextentry;
		      if(cpu->entrytype != 0)
		        break;

		      if(cpu->cpuflags & 0x1){
 		        HALT_ON_ERRORCOND( *num_pcpus < MAX_PCPU_ENTRIES);
						_XDPRINTF_("\nCPU (0x%08x) #%u: lapic id=0x%02x, ver=0x%02x, cpusig=0x%08x",
		          (uint32_t)cpu, i, cpu->lapicid, cpu->lapicver, cpu->cpusig);
		        pcpus[i].lapic_id = cpu->lapicid;
		        pcpus[i].lapic_ver = cpu->lapicver;
		        pcpus[i].lapic_base = mpctable->lapicaddr;
		        pcpus[i].isbsp = cpu->cpuflags & 0x2;
		        *num_pcpus = *num_pcpus + 1;
		      }

		      addrofnextentry += sizeof(MPENTRYCPU);
		    }
		  }


			return 1;
	}


	return 1;

}


static int mp_checksum(unsigned char *mp, int len){
	int sum = 0;

	while (len--)
  	sum += *mp++;

	return sum & 0xFF;
}


//returns 1 if MP table found and populates mpfp with MP table pointer
//returns 0 if no MP table and makes mpfp=NULL
static uint32_t mp_scan_config(uint32_t base, uint32_t length, MPFP **mpfp){
	uint32_t *bp = (uint32_t *)base;
  MPFP *mpf;

  _XDPRINTF_("\n%s: Finding MP table from 0x%08x for %u bytes",
                        __func__, (uint32_t)bp, length);

  while (length > 0) {
     mpf = (MPFP *)bp;
     if ((*bp == MPFP_SIGNATURE) &&
                    (mpf->length == 1) &&
                    !mp_checksum((unsigned char *)bp, 16) &&
                    ((mpf->spec_rev == 1)
                     || (mpf->spec_rev == 4))) {

                        _XDPRINTF_("\n%s: found SMP MP-table at 0x%08x",
                               __func__, (uint32_t)mpf);

												*mpfp = mpf;
                        return 1;
      }
     bp += 4;
     length -= 16;
  }

  *mpfp=0;
	return 0;
}


uint32_t mp_getebda(void){
  uint16_t ebdaseg;
  uint32_t ebdaphys;
  //get EBDA segment from 040E:0000h in BIOS data area
  ebdaseg= * ((uint16_t *)0x0000040E);
  //convert it to its 32-bit physical address
  ebdaphys=(uint32_t)(ebdaseg * 16);
	return ebdaphys;
}

//------------------------------------------------------------------------------
uint32_t _ACPIGetRSDPComputeChecksum(uint32_t spaddr, uint32_t size){
  char *p;
  char checksum=0;
  uint32_t i;

  p=(char *)spaddr;

  for(i=0; i< size; i++)
    checksum+= (char)(*(p+i));

  return (uint32_t)checksum;
}

//get the physical address of the root system description pointer (rsdp)
//return 0 if not found
ACPI_RSDP * ACPIGetRSDP(void){
  uint16_t ebdaseg;
  uint32_t ebdaphys;
  uint32_t i, found=0;
  ACPI_RSDP *rsdp;

  //get EBDA segment from 040E:0000h in BIOS data area
  ebdaseg= * ((uint16_t *)0x0000040E);
  //convert it to its 32-bit physical address
  ebdaphys=(uint32_t)(ebdaseg * 16);
  //search first 1KB of ebda for rsdp signature (8 bytes long)
  for(i=0; i < (1024-8); i+=16){
    rsdp=(ACPI_RSDP *)(ebdaphys+i);
    if(rsdp->signature == ACPI_RSDP_SIGNATURE){
      if(!_ACPIGetRSDPComputeChecksum((uint32_t)rsdp, 20)){
        found=1;
        break;
      }
    }
  }

  if(found)
    return rsdp;

  //search within BIOS areas 0xE0000 to 0xFFFFF
  for(i=0xE0000; i < (0xFFFFF-8); i+=16){
    rsdp=(ACPI_RSDP *)i;
    if(rsdp->signature == ACPI_RSDP_SIGNATURE){
      if(!_ACPIGetRSDPComputeChecksum((uint32_t)rsdp, 20)){
        found=1;
        break;
      }
    }
  }

  if(found)
    return rsdp;

  return (ACPI_RSDP *)NULL;
}
//------------------------------------------------------------------------------

