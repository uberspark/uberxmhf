
//-----------------------------
#include <windows.h>
#include <powrprof.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/timeb.h>
#include "usb.h"

// types
#ifndef MIN
#define MIN(a,b)	((a)<(b)?(a):(b))
#endif
typedef unsigned int U32;
typedef unsigned char U8;

#define MAX_TIME 3000

static unsigned char abData[16384];

// USB device specific definitions
#define VENDOR_ID			0xFFFF
#define PRODUCT_ID		0x0004
#define BM_REQUEST_TYPE		(2<<5)

//#define BULK_IN_EP			0x82
//#define BULK_OUT_EP			0x05

// this structure should match with the expectations of the 'custom' device!
typedef struct {
	U32		dwAddress;
	U32		dwLength;
} TMemoryCmd;


static struct usb_device * find_device(int iVendor, int iProduct)
{
	struct usb_bus	*usb_bus;
	struct usb_device *dev;	
	
	for (usb_bus = usb_get_busses(); usb_bus; usb_bus = usb_bus->next) {
		for (dev = usb_bus->devices; dev; dev = dev->next) {
			if ((dev->descriptor.idVendor == iVendor) && 
				(dev->descriptor.idProduct == iProduct)) {
				return dev;
			}
		}
	}
	return NULL;
}

//set device state (TRUSTED=1, UNTRUSTED=0)
//return 1 if success, 0 if failure
int usbdevice_setdevicestate(struct usb_dev_handle *hdl, int state){
	int i;
	TMemoryCmd MemCmd;

	// send a vendor request to check button status
	MemCmd.dwAddress = state; 
	MemCmd.dwLength = 0x0;
	i = usb_control_msg(hdl, BM_REQUEST_TYPE, 0xB0, 0, 0, (char *)&MemCmd, sizeof(MemCmd), 1000);
	if (i < 0){
		fprintf(stderr, "usb_control_msg failed %d\n", i);
		return 0;		
	}

	return 1;
}


//return 1 if the button was pressed, else 0
int usbdevice_checkbuttonstatus(struct usb_dev_handle *hdl){
	int i;
	char buttonstatus;	
	TMemoryCmd MemCmd;

	// send a vendor request to check button status
	MemCmd.dwAddress = 0x0;
	MemCmd.dwLength = 0x0;
	i = usb_control_msg(hdl, BM_REQUEST_TYPE, 0xA0, 0, 0, (char *)&MemCmd, sizeof(MemCmd), 1000);
	if (i < 0){
		fprintf(stderr, "usb_control_msg failed %d\n", i);
		return 0;		
	}

	//fprintf(stderr, "request success!\n");

	i = usb_bulk_read(hdl, 0x82, (char *)&buttonstatus, sizeof(buttonstatus), 2000);
	if (i < 0) {
		fprintf(stderr, "usb_bulk_read failed %d\n", i);
		return 0;
	}

	if(buttonstatus){
		printf("\nbutton press detected...");
		return 1;
	}


	return 0;
}

int main(int argc, char *argv[])
{
	struct usb_device *dev;	
	struct usb_dev_handle *hdl;
	int i;

	usb_init();
	usb_find_busses();
	usb_find_devices();
	
	dev = find_device(VENDOR_ID, PRODUCT_ID);
	if (dev == NULL) {
		fprintf(stderr, "device not found\n");
		return -1;
	}
	
	hdl = usb_open(dev);
	
	i = usb_set_configuration(hdl, 1);
	if (i < 0) {
		fprintf(stderr, "usb_set_configuration failed\n");
	}
	
	i = usb_claim_interface(hdl, 0);
	if (i < 0) {
		fprintf(stderr, "usb_claim_interface failed %d\n", i);
		return -1;
	}

	//for the first time we start, get the status from VMM and set it
	if(!usbdevice_setdevicestate(hdl,0)){ //now force to trusted
		fprintf(stderr, "\nunable to set device state");
		return -1;
	}

	while(1){ 	//the main while loop we never exit

		printf("\nWaiting for lockdown device command...");
		while(!usbdevice_checkbuttonstatus(hdl))	
			;
		printf("\ngot button press");

		//SetSuspendState(TRUE, FALSE,FALSE);
	
		printf("\ngot awake...");

		//get state from vmm and set it
		if(!usbdevice_setdevicestate(hdl, 0)){ //now force to trusted
			fprintf(stderr, "\nunable to set device state");
			return -1;
		}
	}

	usb_release_interface(hdl, 0);
	usb_close(hdl);

	return 0;
}



	

