//firmware reset code for lockdown
//experimenting with VGA and disk resets for switching between
//environments under lockdown
//author: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h>

/*//------------------------------------------------------------------------------
//PCI subsystem glue code
//we support only type-1 direct access which should not be a problem
//with any system manufactured after the year 2001

//function checks to see if type-1 direct acccess is supported
//by the system
//return 1 on success else 0
static int pci_check_type1(void){
	unsigned long flags;
	unsigned int tmp;
	int works = 0;
 
  outb(0x01, 0xCFB);
  tmp = inl(0xCF8);
  outl(0x80000000, 0xCF8);
  if (inl(0xCF8) == 0x80000000)
  	works = 1;
 	
	 outl(tmp, 0xCF8);
  return works;
}

int pci_initialize(void){
	return(pci_check_type1());
}

#define PCI_CONF1_ADDRESS(bus, devfn, reg) \
        (0x80000000 | ((reg & 0xF00) << 16) | (bus << 16) \
        | (devfn << 8) | (reg & 0xFC))
#define PCI_DEVFN(device, func) ((((device) & 0x1f) << 3) | ((func) & 0x07) )

//returns 1 on success, 0 on error
int emhf_baseplatform_arch_x86_pci_conf1_read(unsigned int bus, unsigned int device, unsigned int function,
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
int emhf_baseplatform_arch_x86_pci_conf1_write(unsigned int bus, unsigned int device, unsigned int function,
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

#undef PCI_CONF1_ADDRESS
*/

//------------------------------------------------------------------------------
//VGA compatible adapter reset
#define	COLUMNS	80
#define LINES		25

// this will reset a VGA compatible graphics adapter to text mode
void hw_vga_reset(void){
  /* The following VGA state was saved from a chip in text mode 3. */
  static unsigned char regs[] = {
    /* Sequencer registers */
    0x03, 0x00, 0x03, 0x00, 0x02,
    /* CRTC registers */
    0x5f, 0x4f, 0x50, 0x82, 0x55, 0x81, 0xbf, 0x1f, 0x00, 0x4f, 0x20,
    0x0e, 0x00, 0x00, 0x01, 0xe0, 0x9c, 0x8e, 0x8f, 0x28, 0x1f, 0x96,
    0xb9, 0xa3, 0xff,
    /* Graphic registers */
    0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x0e, 0x00, 0xff,
    /* Attribute registers */
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x14, 0x07, 0x38, 0x39, 0x3a,
    0x3b, 0x3c, 0x3d, 0x3e, 0x3f, 0x0c, 0x00, 0x0f, 0x08, 0x00
  };

  int i, j = 0;
  volatile unsigned char tmp;
	u32 video;

  video = 0xB8000;

  tmp = inb(0x3da);
  outb(0x00, 0x3c0);
  
  for ( i = 0; i < 5;  i ++ )
    outw((u32)(regs[j ++] << 8) | i, 0x3c4);
  
  //Ensure CRTC registers 0-7 are unlocked by clearing bit 7 of CRTC[17]. 
  outw((u32)((regs[5+17] & 0x7F) << 8) | 17, 0x3d4);
  
  for ( i = 0; i < 25; i ++ ) 
    outw((u32)(regs[j ++] << 8) | i, 0x3d4);
  
  for ( i = 0; i < 9;  i ++ )
    outw((u32)(regs[j ++] << 8) | i, 0x3ce);
  
  for ( i = 0; i < 21; i ++ )
  {
    tmp = inb(0x3da);
    outb((u32)i, 0x3c0); 
    outb(regs[j ++], 0x3c0);
  }
  
  tmp = inb(0x3da);
  outb(0x20, 0x3c0);

	//clear the screen
  outw(10 + (1 << (5 + 8)), 0x3d4); // cursor off
	{
		u16 *vidmem = (u16 *)video;
		int i;
		
		for(i=0; i < (COLUMNS * LINES); i++)
			vidmem[i]=0x0f20;
	}
	outw(10 + (0 << (5 + 8)), 0x3d4); // cursor on
}


//------------------------------------------------------------------------------
//low-level ATA/ATAPI bus reset
//controller at 0:1f:2 for hp8540p/corei5

#define ATA_DEVICECONTROLREGISTER		0x3F6

#define ATA_STATUS_BSY	((u8)1 << 7)
#define ATA_STATUS_RDY  ((u8)1 << 6)
#define ATA_STATUS_DRQ	((u8)1 << 3)
#define ATA_STATUS_ERR	((u8)1 << 0)
#define ATA_STATUS_DF		((u8)1 << 5)

u32 diskpciconf[16];

void hw_disk_savepciconf(void){
	int i;
	printf("\n%s: starting...", __FUNCTION__);
	for(i=0; i < 16; i++)
			emhf_baseplatform_arch_x86_pci_type1_read(0, 0x1f, 0x2, i*4, 4, &diskpciconf[i]);
	printf("\n%s: done.", __FUNCTION__);
}

void hw_disk_restorepciconf(void){
	int i;
	printf("\n%s: starting...", __FUNCTION__);
	for(i=0; i < 16; i++)
			emhf_baseplatform_arch_x86_pci_type1_write(0, 0x1f, 0x2, i*4, 4, diskpciconf[i]);
	printf("\n%s: done.", __FUNCTION__);
}


void hw_disk_reset(void){
	u8 status;
	
	outb(0x04, ATA_DEVICECONTROLREGISTER); 	//do a software reset on the bus
	outb(0x00, ATA_DEVICECONTROLREGISTER);	//reset bus to normal operation
	inb(ATA_DEVICECONTROLREGISTER);
	inb(ATA_DEVICECONTROLREGISTER);
	inb(ATA_DEVICECONTROLREGISTER);
	inb(ATA_DEVICECONTROLREGISTER);					//may take upto 4 tries for status
	
	status=inb(ATA_DEVICECONTROLREGISTER);
	while( !(!(status & ATA_STATUS_BSY) && (status & ATA_STATUS_RDY)) )
		status=inb(ATA_DEVICECONTROLREGISTER);
}

void hw_disk_printpciconf(void){
	u32 value;
	int i;
	
	printf("\nconf dump for 0:1f:2...");
	for(i=0; i < 16; i++){
			emhf_baseplatform_arch_x86_pci_type1_read(0, 0x1f, 0x2, i*4, 4, &value);
   		printf("\nat offset 0x%02x: 0x%08x", (i*4), value);
  }
}
