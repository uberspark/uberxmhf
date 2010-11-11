//------------------------------------------------------------------------------
// hcd-uhci.c
//
// host controller driver for UHCI host controllers
// author: amit vasudevan (amitvasudevan@acm.org)
//------------------------------------------------------------------------------

#include <types.h>
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <machine.h>
#include <error.h>

#include "hcd-uhci.h"

//------------------------------------------------------------------------------
// delay glue
// this is CPU specific
// TODO: calibration routine to make this generic
#define TIMEOUT_1MS	((0x40000000ULL * 2) / 1000)

void delay_mdelay(unsigned int msec)
{
	unsigned long long cycles = TIMEOUT_1MS * msec;
	unsigned long long diff;
	unsigned int lo_before, hi_before, lo_after, hi_after;

	__asm__ __volatile__ ("rdtsc" : "=a" (lo_before), "=d"(hi_before));
	do 
	{
		__asm__ __volatile__ ("rdtsc" : "=a" (lo_after), "=d"(hi_after));
		diff = (((unsigned long long)hi_after << 32) | lo_after) - (((unsigned long long)hi_before << 32) | lo_before);
	} while (diff < cycles);
}


//------------------------------------------------------------------------------
// PCI bus glue
#define PCI_CONF1_ADDRESS(bus, devfn, reg) \
        (0x80000000 | ((reg & 0xF00) << 16) | (bus << 16) \
        | (devfn << 8) | (reg & 0xFC))

#define PCI_DEVFN(device, func)   ((((device) & 0x1f) << 3) | ((func) & 0x07))
#define PCI_DEV(devfn)         	(((devfn) >> 3) & 0x1f)
#define PCI_FUNC(devfn)         ((devfn) & 0x07)

//returns 1 on success, 0 on error
int pci_conf1_read(unsigned int bus, unsigned int device, unsigned int function,
							unsigned int reg, int len, u32 *value){
        unsigned long flags;
        unsigned int devfn=PCI_DEVFN(device, function);

        if ((bus > 255) || (devfn > 255) || (reg > 4095)) {
                *value = -1;
                return 0;
        }

        outl(PCI_CONF1_ADDRESS(bus, devfn, reg), 0xCF8);

        switch (len) {
        case 1:
                *value = inb(0xCFC + (reg & 3));
                break;
        case 2:
                *value = inw(0xCFC + (reg & 2));
                break;
        case 4:
                *value = inl(0xCFC);
                break;
        }
        
				return 1;
}

//returns 1 on success, 0 on failure
int pci_conf1_write(unsigned int bus, unsigned int device, unsigned int function,
	unsigned int reg, int len, u32 value){
        unsigned long flags;
        unsigned int devfn=PCI_DEVFN(device, function);

        if ((bus > 255) || (devfn > 255) || (reg > 4095))
                return 0;

        outl(PCI_CONF1_ADDRESS(bus, devfn, reg), 0xCF8);

        switch (len) {
        case 1:
                outb((u8)value, 0xCFC + (reg & 3));
                break;
        case 2:
                outw((u16)value, 0xCFC + (reg & 2));
                break;
        case 4:
                outl((u32)value, 0xCFC);
                break;
        }

        return 1;
}

//------------------------------------------------------------------------------



//------------------------------------------------------------------------------
// mm glue
// set a given page attributes to cache-disable or cache-enable

// note: our runtime has 2M pages mapped
#define MM_PAGE_CACHE_DISABLE	0x0
#define MM_PAGE_CACHE_ENABLE	0x1

void mm_setpagecaching(u32 vaddr, u32 cacheenable){
	extern u32 __runtime_pdts[];
	
	u32 aligned_vaddr = PAGE_ALIGN_2M(vaddr);
	u32 pdt_index = aligned_vaddr / PAGE_SIZE_2M;
	pdt_t  pdt;
	
	pdt=(pdt_t)__runtime_pdts;

	printf("\n%s:enter", __FUNCTION__);
	printf("\n	vaddr=0x%08x, aligned=0x%08x", vaddr, aligned_vaddr);
	printf("\n	index=%u, before=0x%016x", pdt_index,
		pdt[pdt_index]);

	if(cacheenable == MM_PAGE_CACHE_DISABLE)
		pdt[pdt_index] |= (u64)_PAGE_PCD;
	else
		pdt[pdt_index] &= ~((u64)_PAGE_PCD);

	printf("\n	after=0x%016x", pdt[pdt_index]);
		
	//reload CR3	
	{
		u32 cr3;
		cr3 = read_cr3();
		write_cr3(cr3);
	}

	printf("\n%s:leave", __FUNCTION__);
}

//------------------------------------------------------------------------------


//test controller at
//pci b:d:f, 00:1a:00

u32 uhci_iobase=0;
u32 b=0x00, d=0x1a, f=0x00;	//our UHCI HC
u8 uhci_reg_sofmodify_value = 0;

void uhci_setup(void){
	
	/*
		first determine this is a UHCI controller by reading CLASSC
		from PCI configuration space
		
		UHCI SPEC
		09-0Bh CLASSC Class Code RO
		
		Bit Description
		23:16 Base Class Code (BASEC). 0Ch= Serial Bus controller.
		15:8 Sub-Class Code (SCC). 03h=Universal Serial Bus Host Controller.
		7:0 Programming Interface (PI). 00h=No specific register level programming interface defined.
	*/
	
	{
		u32 classc;
		u32 basec, scc, pi;
		pci_conf1_read(b, d, f, 0x08, 4, &classc);
		printf("\n%s: classc=0x%08x", __FUNCTION__, classc);
		basec = ((classc & 0xFF000000UL) >> 24);
		scc = ((classc & 0x00FF0000UL) >> 16);
		pi = ((classc & 0x0000FF00UL) >> 8);
	
		ASSERT( ((basec == 0x0C) && (scc == 0x03) && (pi == 0x00)) );
	}
	
	/*
		obtain serial bus release number by reading SBRN from
		PCI configuration space
		
		UHCI SPEC
		60h SBRN Serial Bus Release Number RO
		
		Bit Description
		7:0 Serial Bus Specification Release Number. All other combinations are reserved.
		Bits[7:0] Release Number
		00h Pre-release 1.0
		10h Release 1.0
	*/
	{
		u32 sbrn;
		pci_conf1_read(b, d, f, 0x60, 1, &sbrn);
		printf("\n%s: sbrn=0x%02x", __FUNCTION__, sbrn);
		ASSERT( ( (sbrn == 0x10) ) );
	}

	/*
		finally obtain the base IO region of the UHCI HC for
		communication by reading USBBASE from PCI configuration
		space
		
		UHCI SPEC
		20-23h USBBASE IO Space Base Address R/W
		Bit Description
		31:16 Reserved. Hardwired to 0s. Must be written as 0s.
		15:5 Index Register Base Address. Bits [15:5] correspond to I/O address signals AD [15:5],
		respectively.
		4:1 Reserved. Read as 0.
		0 Resource Type Indicator (RTE)—RO. This bit is hardwired to 1 indicating that the base address
		field in this register maps to I/O space.	
	*/
		
	{
		u32 usbbase;
		
		pci_conf1_read(b, d, f, 0x20, 4, &usbbase);
		printf("\n%s: usbbase=0x%08x", __FUNCTION__, usbbase);
		ASSERT( ((usbbase & 0xFFFF0000UL) == 0) );
		ASSERT( ((usbbase & 0x00000001UL) == 1) );
		ASSERT( ((usbbase & 0x0000001EUL) == 0) );
		
		uhci_iobase = usbbase & 0x0000FFE0UL;
		printf("\n%s: uhci_iobase = 0x%08x", __FUNCTION__, uhci_iobase);
	}
		
	//enable DMA master capability, memory and IO access
	//by writing to the COMMAND register in PCI configuration
	//space
#define PCI_COMMAND_IO          0x1     // Enable response in I/O space 
#define PCI_COMMAND_MEMORY      0x2     // Enable response in Memory space 
#define PCI_COMMAND_MASTER      0x4     // Enable bus mastering 
	
	{
		u32 value;	
		pci_conf1_read(b, d, f, 0x04, 2, &value);	
		printf("\n%s: PCI command=0x%04x", __FUNCTION__, value);
		value |= (PCI_COMMAND_IO | PCI_COMMAND_MEMORY | PCI_COMMAND_MASTER);
		pci_conf1_write(b, d, f, 0x04, 2, value);
	}	

}

// assumes control of UHCI HC and resets it
void uhci_assumecontrol(void){
	// turn off legacy USB support so that BIOS does not use this
	// HC anymore. this can be done via LEGSUP in PCI configuration
	// space
	// UHCI SPEC
	// LEGSUP - LEGACY SUPPORT REGISTER (PCI Configuration - Function 2)
	// PCI Address Offset: C0-C1h

	// set all r/w-c bits to 0 and all r/w bits to 0
	// this turns off PIRQ enable and SMI enable thereby removing BIOS
	// from the equation
	{
		u32 legsup_rwc = 0x8f00;		// the R/WC bits 
		pci_conf1_write(b, d, f, 0xC0, 2, legsup_rwc);
	}

	//store contents of SOFMODIFY register as it is lost
	//after a reset
	uhci_reg_sofmodify_value = inb(UHCI_REG_SOFMODIFY);
	printf("\nUHCI_REG_SOFMODIFY(before)=0x%02x", uhci_reg_sofmodify_value);

	//reset the HC 
	outw(UHCI_USBCMD_HCRESET, UHCI_REG_USBCMD);
	delay_mdelay(1);
	if (inw(UHCI_REG_USBCMD) & UHCI_USBCMD_HCRESET)
		printf("\nWarning: HCRESET not completed yet!");

	//disable interrupt requests and stop HC
	outw(0, UHCI_REG_USBINTR);
	outw(0, UHCI_REG_USBCMD);
	
	//
	printf("\nUHCI_REG_SOFMODIFY(after)=0x%02x", inb(UHCI_REG_SOFMODIFY));
	
	//restore SOFMODIFY register value
	outb(uhci_reg_sofmodify_value, UHCI_REG_SOFMODIFY);
	printf("\nUHCI_REG_SOFMODIFY(restored)=0x%02x", inb(UHCI_REG_SOFMODIFY));
	
}	

//activate a port on the HC
//for now we assume device to be connected
void uhci_activateport(void){
	//check current connect status
	u16 portstatus;
	u32 port= UHCI_REG_PORTSC1; //our device connected to this port

	printf("\n%s: enter", __FUNCTION__);

	//get current port status
	portstatus = inw(port);
	printf("\n	current port status=0x%04x", portstatus);
	
	//determine if our device is currently connected
	if(!(portstatus &  UHCI_PORTSC_CCS)){
		printf("\n	no device connected to port. HALTING!");
		HALT();
	}
	
	//ok, our device is connected to the port, clear the connect
	//status change if set
	printf("\n	device connected to port, clearing CSC...");	
	portstatus |= UHCI_PORTSC_CSC;	//its a r/w-c so we write 1 to clear it
	outw(portstatus, port);
	portstatus = inw(port);
	printf("done -> status=0x%04x", portstatus);
	
	//enable port
	printf("\n	enabling port...");
	portstatus |= UHCI_PORTSC_PE;
	outw(portstatus, port);
	while( !(inw(port) & UHCI_PORTSC_PE) );
	portstatus = inw(port);
	printf("done ->status=0x%04x", portstatus); 

	//check for device speed
	if(portstatus & UHCI_PORTSC_LSDA)
		printf("\n	LS device attached");
	else
		printf("\n	FS device attached");
	
	//reset this port
	printf("\n	resetting port...");
	portstatus |= UHCI_PORTSC_PR;
	outw(portstatus, port);
	delay_mdelay(100);	// UHCI spec says 10ms minimum, we just do 100ms 
	portstatus &= ~(UHCI_PORTSC_PR);
	outw(portstatus, port);	
	portstatus = inw(port);
	printf("done ->status=0x%04x", portstatus); 

	//the port will be disabled due to the reset, clear
	//the disabled flag and re-enable port
	printf("\n	clearing port enable/disable...");	
	portstatus |= UHCI_PORTSC_PEC;	//its a r/w-c so we write 1 to clear it
	outw(portstatus, port);
	portstatus = inw(port);
	printf("done -> status=0x%04x", portstatus);

	printf("\n	re-enabling port...");
	portstatus |= UHCI_PORTSC_PE;
	outw(portstatus, port);
	while( !(inw(port) & UHCI_PORTSC_PE) );
	portstatus = inw(port);
	printf("done ->status=0x%04x", portstatus); 

	//get current port status
	portstatus = inw(port);
	printf("\n	current port status=0x%04x", portstatus);
	
	//determine if our device is currently connected
	if(!(portstatus &  UHCI_PORTSC_CCS)){
		printf("\n	no device connected to port. HALTING!");
		HALT();
	}
	
	//ok, our device is connected to the port, clear the connect
	//status change if set
	printf("\n	device connected to port, clearing CSC...");	
	portstatus |= UHCI_PORTSC_CSC;	//its a r/w-c so we write 1 to clear it
	outw(portstatus, port);
	portstatus = inw(port);
	printf("done -> status=0x%04x", portstatus);
	
	//check for device speed
	if(portstatus & UHCI_PORTSC_LSDA)
		printf("\n	LS device attached");
	else
		printf("\n	FS device attached");

	printf("\n%s: leave", __FUNCTION__);

}

//our USB SETUP packet
USB_TOKEN_SETUP usb_token_setup;
USB_DESCRIPTOR_DEVICE usb_device_descriptor;



//------------------------------------------------------------------------------
//setup UHCI schedule
//
//
UHCI_QH *schedule_interrupt_qh = NULL;
UHCI_QH *schedule_control_qh = NULL;
UHCI_QH *schedule_bulk_qh = NULL;
UHCI_QH *schedule_termination_qh = NULL;
UHCI_TD *schedule_isochronous_td = NULL;
UHCI_FRAME *schedule_framelist = NULL;
//TDs for the control QH
UHCI_TD *schedule_control_qh_td0 = NULL;
UHCI_TD *schedule_control_qh_td1 = NULL;
UHCI_TD *schedule_control_qh_td2 = NULL;

#if 0
void uhci_setupschedule(void){
	extern u32 __uhci_framelist_base[];
	extern u32 __uhci_qh_base[];
	extern u32 __uhci_td_base[];

	//clear our FRAME, QH and TD pages	
	memset((void *)__uhci_framelist_base, 0, 4096);
	memset((void *)__uhci_qh_base, 0, 4096);
	memset((void *)__uhci_td_base, 0, 4096);

	//allocate our frame list
	schedule_framelist = (UHCI_FRAME *)__uhci_framelist_base; 
	printf("\nfl=0x%08x", schedule_framelist);
	
	//make sure all our frame list entries except for the 1st one are marked
	//invalid
	{
		int i;
		for (i=0; i < 1024; i++)
			schedule_framelist[i].t = UHCI_FRAME_INVALID;
	}

	//allocate our QHs
	schedule_interrupt_qh =  (UHCI_QH *)__uhci_qh_base; 
	schedule_control_qh = (UHCI_QH *)((u32)__uhci_qh_base + 16); 
	schedule_bulk_qh = (UHCI_QH *)((u32)__uhci_qh_base + (16*2)); 
	schedule_termination_qh = (UHCI_QH *)((u32)__uhci_qh_base + (16*3));
	
	printf("\nqhs(i,c,b,t)=0x%08x,0x%08x,0x%08x,0x%08x",
		schedule_interrupt_qh, schedule_control_qh, schedule_bulk_qh, schedule_termination_qh);

	//allocate our isochronous TD first then the 3 TDs for our 
	//control QH
	schedule_isochronous_td = (UHCI_TD *)__uhci_td_base; 
	schedule_control_qh_td0 = (UHCI_TD *)((u32)__uhci_td_base + 32); 
	schedule_control_qh_td1 = (UHCI_TD *)((u32)__uhci_td_base + (32*2)); 
	schedule_control_qh_td2 = (UHCI_TD *)((u32)__uhci_td_base + (32*3)); 
	
	printf("\ntds(i,cqtd0,cqtd1,cqtd2)=0x%08x,0x%08x,0x%08x,0x%08x",
		schedule_isochronous_td, schedule_control_qh_td0, 
		schedule_control_qh_td1,
		schedule_control_qh_td2);
		
	//link first frame to isochronous td
	schedule_framelist[0].t= UHCI_FRAME_VALID;
	schedule_framelist[0].q = UHCI_FRAME_FLP_TD;
	schedule_framelist[0].FLP = ((u32)schedule_isochronous_td >> 4);

	//link isochronous td to interrupt QH and fill in a dummy OUT td with 0 bytes
	schedule_isochronous_td->LP = ((u32)schedule_interrupt_qh >> 4);		                                                                                                                                                                  
	schedule_isochronous_td->Vf= UHCI_TD_BREADTHFIRST;	
	schedule_isochronous_td->q = UHCI_TD_LP_QH;
	schedule_isochronous_td->t = UHCI_TD_LP_VALID;
	schedule_isochronous_td->SPD=0;
	schedule_isochronous_td->error = 3;	//3 retry maximum
	schedule_isochronous_td->LS = 0;	//FS device
	schedule_isochronous_td->IOS = 1; //isochronous
	schedule_isochronous_td->IOC = 0; //issue interrupt on completion of this frame
	schedule_isochronous_td->status = UHCI_TD_STATUS_ACTIVE; //execute this TD
	schedule_isochronous_td->MaxLen = 0;
	schedule_isochronous_td->D = 0; //start with 0
	schedule_isochronous_td->EndPt = 0; //endpoint 0
	schedule_isochronous_td->deviceaddr = 0; //device 0
	schedule_isochronous_td->PID = UHCI_TD_PID_OUT;
	schedule_isochronous_td->tdbufferpointer = 0;
	printf("\nschedule_isochronous_td->LP=0x%08x", schedule_isochronous_td->LP);
	{
		u32 *value;
		value = (u32 *)schedule_isochronous_td;
		printf("\nDWORD value=0x%08x", *value);
	}
	
		
	//make interrupt QH null and link to control QH
	schedule_interrupt_qh->t = UHCI_QH_QHLP_VALID;
	schedule_interrupt_qh->q = UHCI_QH_QHLP_QH;
	schedule_interrupt_qh->QHLP = (u32)schedule_control_qh >> 4;
	schedule_interrupt_qh->queue_t = UHCI_QH_QUEUE_INVALID;
	schedule_interrupt_qh->queue_q = 0;
	schedule_interrupt_qh->QELP = 0;
	printf("\nschedule_interrupt_qh->QHLP=0x%08x",schedule_interrupt_qh->QHLP);
	{
		u32 *value;
		value = (u32 *)schedule_interrupt_qh;
		printf("\nDWORD value=0x%08x", *value);
	}
	
	
	//make control QH link to bulk QH and tie in control QH TDs
	schedule_control_qh->t = UHCI_QH_QHLP_VALID;
	schedule_control_qh->q = UHCI_QH_QHLP_QH;
	schedule_control_qh->QHLP = (u32)schedule_bulk_qh >> 4;
	schedule_control_qh->queue_t = UHCI_QH_QUEUE_VALID;
	schedule_control_qh->queue_q = UHCI_QH_QELP_TD;
	schedule_control_qh->QELP = (u32)schedule_control_qh_td0 >> 4;

	printf("\nschedule_control_qh->QHLP=0x%08x",schedule_control_qh->QHLP);
	{
		u32 *value;
		value = (u32 *)schedule_control_qh;
		printf("\nDWORD value=0x%08x", *value);
	}

	printf("\nschedule_control_qh->QELP=0x%08x",schedule_control_qh->QELP);
	{
		u32 *value;
		value = (u32 *) ((u32)schedule_control_qh+4);
		printf("\nDWORD value=0x%08x", *value);
	}


	
	schedule_control_qh_td0->LP = ((u32)schedule_control_qh_td1 >> 4);		                                                                                                                                                                  
	schedule_control_qh_td0->Vf= UHCI_TD_DEPTHFIRST;	//depth first
	schedule_control_qh_td0->q = UHCI_TD_LP_TD;
	schedule_control_qh_td0->t = UHCI_TD_LP_VALID;

	printf("\nschedule_control_qh_td0->LP=0x%08x",schedule_control_qh_td0->LP);
	{
		u32 *value;
		value = (u32 *) (schedule_control_qh_td0);
		printf("\nDWORD value=0x%08x", *value);
	}

	
	schedule_control_qh_td1->LP = ((u32)schedule_control_qh_td2 >> 4);		                                                                                                                                                                  
	schedule_control_qh_td1->Vf= UHCI_TD_DEPTHFIRST;	//depth first
	schedule_control_qh_td1->q = UHCI_TD_LP_TD;
	schedule_control_qh_td1->t = UHCI_TD_LP_VALID;

	printf("\nschedule_control_qh_td1->LP=0x%08x",schedule_control_qh_td1->LP);
	{
		u32 *value;
		value = (u32 *) (schedule_control_qh_td1);
		printf("\nDWORD value=0x%08x", *value);
	}

	
	schedule_control_qh_td2->LP = 0;		                                                                                                                                                                  
	schedule_control_qh_td2->Vf= 0;	
	schedule_control_qh_td2->q = 0;
	schedule_control_qh_td2->t = UHCI_TD_LP_INVALID;

	//make bulk QH null and point to termination QH
	schedule_bulk_qh->t = UHCI_QH_QHLP_VALID;
	schedule_bulk_qh->q = UHCI_QH_QHLP_QH;
	schedule_bulk_qh->QHLP = (u32)schedule_termination_qh >> 4;
	schedule_bulk_qh->queue_t = UHCI_QH_QUEUE_INVALID;
	schedule_bulk_qh->queue_q = 0;
	schedule_bulk_qh->QELP = 0;
	printf("\nschedule_bulk_qh->QHLP=0x%08x",schedule_bulk_qh->QHLP);
	{
		u32 *value;
		value = (u32 *)schedule_bulk_qh;
		printf("\nDWORD value=0x%08x", *value);
	}


	//make termination QH null and terminate
	schedule_bulk_qh->t = UHCI_QH_QHLP_INVALID;
	schedule_bulk_qh->q = 0;
	schedule_bulk_qh->QHLP = 0;
	schedule_bulk_qh->queue_t = UHCI_QH_QUEUE_INVALID;
	schedule_bulk_qh->queue_q = 0;
	schedule_bulk_qh->QELP = 0;
			
}

#else	//non-standard schedule, 1 QH and TDs linked in

void uhci_setupschedule(void){
	#define UHCI_FRAMELIST_BASE 	0x80000000
	#define UHCI_QH_BASE					0x80002000
	#define UHCI_TD_BASE					0x80004000
	
	//setup our FRAME, QH and TD memory areas to be uncacheable
	mm_setpagecaching(UHCI_FRAMELIST_BASE, MM_PAGE_CACHE_DISABLE);
		
	//clear our FRAME, QH and TD pages	
	memset((void *)UHCI_FRAMELIST_BASE, 0, 4096);
	memset((void *)UHCI_QH_BASE, 0, 4096);
	memset((void *)UHCI_TD_BASE, 0, 4096);

	//allocate our frame list
	schedule_framelist = (UHCI_FRAME *)UHCI_FRAMELIST_BASE; 
	printf("\nfl=0x%08x", schedule_framelist);
	
	//make sure all our frame list entries except for the 1st one are marked
	//invalid
	{
		int i;
		for (i=0; i < 1024; i++)
			schedule_framelist[i].t = UHCI_FRAME_INVALID;
	}

	//allocate our QH
	schedule_control_qh =  (UHCI_QH *)UHCI_QH_BASE; 
	printf("\nqhc=0x%08x", schedule_control_qh);

	//allocate the 3 TDs for our control QH
	schedule_control_qh_td0 = (UHCI_TD *)UHCI_TD_BASE; 
	schedule_control_qh_td1 = (UHCI_TD *)((u32)UHCI_TD_BASE + 32); 
	schedule_control_qh_td2 = (UHCI_TD *)((u32)UHCI_TD_BASE + (32*2)); 
	
	printf("\ntds(cqtd0,cqtd1,cqtd2)=0x%08x,0x%08x,0x%08x",
		schedule_control_qh_td0, 
		schedule_control_qh_td1,
		schedule_control_qh_td2);

	//link first frame to QH
	schedule_framelist[0].t= UHCI_FRAME_VALID;
	schedule_framelist[0].q = UHCI_FRAME_FLP_QH;
	schedule_framelist[0].FLP = ((u32)schedule_control_qh >> 4);


	//make control QH link to NULL and tie in control QH TDs
	schedule_control_qh->t = UHCI_QH_QHLP_INVALID;
	schedule_control_qh->q = 0;
	schedule_control_qh->QHLP = 0;
	schedule_control_qh->queue_t = UHCI_QH_QUEUE_VALID;
	schedule_control_qh->queue_q = UHCI_QH_QELP_TD;
	schedule_control_qh->QELP = (u32)schedule_control_qh_td0 >> 4;

	printf("\nschedule_control_qh->QHLP=0x%08x",schedule_control_qh->QHLP);
	{
		u32 *value;
		value = (u32 *)schedule_control_qh;
		printf("\nDWORD value=0x%08x", *value);
	}

	printf("\nschedule_control_qh->QELP=0x%08x",schedule_control_qh->QELP);
	{
		u32 *value;
		value = (u32 *) ((u32)schedule_control_qh+4);
		printf("\nDWORD value=0x%08x", *value);
	}


	
	schedule_control_qh_td0->LP = ((u32)schedule_control_qh_td1 >> 4);		                                                                                                                                                                  
	schedule_control_qh_td0->Vf= UHCI_TD_DEPTHFIRST;	//depth first
	schedule_control_qh_td0->q = UHCI_TD_LP_TD;
	schedule_control_qh_td0->t = UHCI_TD_LP_VALID;

	printf("\nschedule_control_qh_td0->LP=0x%08x",schedule_control_qh_td0->LP);
	{
		u32 *value;
		value = (u32 *) (schedule_control_qh_td0);
		printf("\nDWORD value=0x%08x", *value);
	}

	
	schedule_control_qh_td1->LP = ((u32)schedule_control_qh_td2 >> 4);		                                                                                                                                                                  
	schedule_control_qh_td1->Vf= UHCI_TD_DEPTHFIRST;	//depth first
	schedule_control_qh_td1->q = UHCI_TD_LP_TD;
	schedule_control_qh_td1->t = UHCI_TD_LP_VALID;

	printf("\nschedule_control_qh_td1->LP=0x%08x",schedule_control_qh_td1->LP);
	{
		u32 *value;
		value = (u32 *) (schedule_control_qh_td1);
		printf("\nDWORD value=0x%08x", *value);
	}

	
	schedule_control_qh_td2->LP = 0;		                                                                                                                                                                  
	schedule_control_qh_td2->Vf= 0;	
	schedule_control_qh_td2->q = 0;
	schedule_control_qh_td2->t = UHCI_TD_LP_INVALID;

}

#endif

//transmit a USB control packet
void uhci_xmit_controlpacket(void){
	//initialze TDs for control packet
	int it;
	
	//SETUP
	schedule_control_qh_td0->SPD=0;
	schedule_control_qh_td0->error = 3;	//3 retry maximum
	schedule_control_qh_td0->LS = 0;	//FS device
	schedule_control_qh_td0->IOS = 0; //non-isochronous
	schedule_control_qh_td0->IOC = 0; //issue interrupt on completion of this frame
	schedule_control_qh_td0->status = UHCI_TD_STATUS_ACTIVE; //execute this TD
		
	schedule_control_qh_td0->MaxLen = sizeof(USB_TOKEN_SETUP)-1;
	schedule_control_qh_td0->D = 0; //start with 0
	schedule_control_qh_td0->EndPt = 0; //endpoint 0
	schedule_control_qh_td0->deviceaddr = 0; //device 0
	schedule_control_qh_td0->PID = UHCI_TD_PID_SETUP;
		
	schedule_control_qh_td0->tdbufferpointer = (u32)&usb_token_setup;
		
	usb_token_setup.request_type = USB_SETUP_XFER_DEVICETOHOST | USB_SETUP_RECIPIENT_DEVICE;
	usb_token_setup.request = USB_SETUP_REQUEST_GET_DESCRIPTOR;
	usb_token_setup.value = 0x0100; //high byte is set to USB_DESCRIPTOR_TYPE_DEVICE, low byte is the starting offset within the descriptor
	usb_token_setup.index = 0; //
	usb_token_setup.length = sizeof(USB_DESCRIPTOR_DEVICE); 
		
	printf("\nsizeof(USB_TOKEN_SETUP)=%u bytes", sizeof(USB_TOKEN_SETUP));
	printf("\nrequest_type=0x%02x, reqeust=0x%02x", usb_token_setup.request_type,
		usb_token_setup.request);
		
	{//DEBUG dump TD
		u32 *value, j;
		value = (u32 *)schedule_control_qh_td0;
		printf("\nTD0 dump:");
		for(j=0; j < 8; j++)	
			printf("\n	0x%08x", value[j]);
	}
		
		
	//IN
	schedule_control_qh_td1->SPD=0;
	schedule_control_qh_td1->error = 3;	//1 retry maximum
	schedule_control_qh_td1->LS = 0;	//FS device
	schedule_control_qh_td1->IOS = 0; //non-isochronous
	schedule_control_qh_td1->IOC = 0; 
	schedule_control_qh_td1->status = UHCI_TD_STATUS_ACTIVE; //execute this TD
		
	schedule_control_qh_td1->MaxLen = sizeof(USB_TOKEN_SETUP)-1;	
	schedule_control_qh_td1->D = 0; //start with 0
	schedule_control_qh_td1->EndPt = 0; //endpoint 0
	schedule_control_qh_td1->deviceaddr = 0; //device 0
	schedule_control_qh_td1->PID = UHCI_TD_PID_IN;
		
	schedule_control_qh_td1->tdbufferpointer = (u32)&usb_device_descriptor;
		
	//OUT
	schedule_control_qh_td2->SPD=0;
	schedule_control_qh_td2->error = 3;	//1 retry maximum
	schedule_control_qh_td2->LS = 0;	//FS device
	schedule_control_qh_td2->IOS = 0; //non-isochronous
	schedule_control_qh_td2->IOC = 1; 
	schedule_control_qh_td2->status = UHCI_TD_STATUS_ACTIVE; //execute this TD
		
	schedule_control_qh_td2->MaxLen = 0x7ff;	//0 bytes
	schedule_control_qh_td2->D = 0; //start with 0
	schedule_control_qh_td2->EndPt = 0; //endpoint 0
	schedule_control_qh_td2->deviceaddr = 0; //device 0
	schedule_control_qh_td2->PID = UHCI_TD_PID_OUT;
		
	schedule_control_qh_td2->tdbufferpointer = 0;

	//ok now initialize the FLBASEADD register with
	//the base address of our frame list
	outl((u32)schedule_framelist, UHCI_REG_FLBASEADD);
	{
		u32 value=inl(UHCI_REG_FLBASEADD);
		printf("\nUHCI_REG_FLBASEADD=0x%08x    ", value);
	}
	
	//initialze FRNUM register to the first index (i.e 0)
	outw(0, UHCI_REG_FRNUM);
	{
		u16 value=inw(UHCI_REG_FRNUM);
		value &= 0x07FF;
		printf("\nUHCI_REG_FRNUM=0x%08x", value);
	}

	{
		u16 portstatus;
		u32 port= UHCI_REG_PORTSC1; //our device connected to this port
		portstatus = inw(port);
		printf("\nportstatus=0x%04x", portstatus);
	
	}

#if 1	
	printf("\nHC processing initiated...");
	//set the HC to run to execute the transaction on the USB bus
	outw( (inw(UHCI_REG_USBCMD) | UHCI_USBCMD_RS | UHCI_USBCMD_MAXP | UHCI_USBCMD_CF), UHCI_REG_USBCMD);
	
	//check for the HC to complete this transaction
	{
		u16 status;
		//u16 value;
			
		do{
			status = inw(UHCI_REG_USBSTS);
			status &= 0x003F;
		}while(!status);
	
		printf("\nHC done processing, status=0x%04x", status);

		//set the HC to stop
		outw( (inw(UHCI_REG_USBCMD) & ~(UHCI_USBCMD_RS)), UHCI_REG_USBCMD);

		//check for errors
		if(status != UHCI_USBSTS_USBINT){
			printf("\nHALT:unable to send control packet: error=0x%04x", status);
			HALT();
		}

		if(schedule_control_qh_td0->status || schedule_control_qh_td1->status
				|| schedule_control_qh_td2->status){
			printf("\nHALT:unable to send control packet: TD errors below");
			printf("\nschedule_control_qh_td0->status=0x%02x", 
				schedule_control_qh_td0->status);
			printf("\nschedule_control_qh_td1->status=0x%02x", 
				schedule_control_qh_td1->status);
			printf("\nschedule_control_qh_td2->status=0x%02x", 
				schedule_control_qh_td2->status);
			HALT();		
		}


	}                                   


	//
	printf("\ncontrol request successfully sent.");
	//debug dump 

#else
	//DEBUG mode
	for(it=0; it < 2; it++)
	{
		
		//set the HC in SWDBG mode
		outw( (inw(UHCI_REG_USBCMD) | UHCI_USBCMD_SWDBG), UHCI_REG_USBCMD);

		//set Run bit, CF bit and UHCI_USBCMD_MAXP and 
		outw( (inw(UHCI_REG_USBCMD) | UHCI_USBCMD_RS | UHCI_USBCMD_MAXP | UHCI_USBCMD_CF), UHCI_REG_USBCMD);

		//after 1 TD has been executed, HC will automatically switch off Run
		//bit, check HCHalted bit in USBSTS register
		{
			u16 status;
			do{
				status = inw(UHCI_REG_USBSTS);
				status &= 0x003F;
			}while( !(status & 0x20) );
			printf("\nUSBSTS=0x%04x", status);
			{
				u16 value=inw(UHCI_REG_FRNUM);
				value &= 0x07FF;
				printf("\nUHCI_REG_FRNUM=0x%08x", value);
			}
		}	

		//dump TD status
		printf("\nschedule_control_qh_td0->status=0x%02x", 
			schedule_control_qh_td0->status);
		printf("\nschedule_control_qh_td1->status=0x%02x", 
			schedule_control_qh_td1->status);
		printf("\nschedule_control_qh_td2->status=0x%02x", 
			schedule_control_qh_td2->status);
		
		//{
		//	USB_TOKEN_SETUP *tok = (USB_TOKEN_SETUP *)schedule_control_qh_td0->tdbufferpointer;
		//	printf("\ntok->request_type=0x%02x", tok->request_type);
		//	printf("\ntok->request=0x%02x", tok->request);
		//	printf("\ntok->value=0x%04x", tok->value);
		//	printf("\ntok->index=0x%04x", tok->index);
		//	printf("\ntok->length=0x%04x", tok->length);
		//}
	
	}
	
#endif	

}

void uhci_debug0(void){
	UHCI_TD td;
	u32 *val;
		
	td.t = 1;
	td.q = 0;
	td.Vf = 0;
	td.LP = 0xABABABC;

	val=(u32 *)&td;
	printf("\nsizeof(UHCI_TD)=%u bytes", sizeof(UHCI_TD));
	printf("\nvalue=0x%08x", *val);
	
}