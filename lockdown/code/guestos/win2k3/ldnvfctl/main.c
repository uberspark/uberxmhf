//lockdown verifier monitor application for windows
// author: amit vasudevan (amitvasudevan@acm.org)

//-----------------------------
#include <windows.h>
#include <powrprof.h>
#include <stdio.h>
//#include <unistd.h>
//#include <sys/timeb.h>
#include "usb.h"
#include "public.h"

// types
#ifndef MIN
#define MIN(a,b)	((a)<(b)?(a):(b))
#endif
typedef unsigned int U32;
typedef unsigned char U8;

//test modes
//#define USB_EP_TEST0    1 //for USB bulk r/w tests
#define LDNVNET_DRV_COMM	2	//communication with lockdown virtual ethernet driver

//#define USB_NETIF_READPACKET  3 //testing reading of n/w packets from verifier via USB


#define MAX_TIME 3000

#define GREEN_LED     1
#define RED_LED       0

static unsigned char abData[16384];

//our verifier Vendor and Product ID
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

//USB bulk r/w test
#if defined (USB_EP_TEST0)

#define ETH_MTU   1500
#define ETH_PACKETSIZE  (ETH_MTU+14)  //6 bytes src MAC, 6 bytes dst MAC and 2 bytes type

char arpreqpacket[] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff,  //6-bytes dest MAC
                       0x06,0x44,0x53,0x06,0x06,0x06,  //6-bytes src MAC
                       0x08, 0x06,  //2-byte type (0x08,0x06 = ethernet ARP)
                       
                       //ARP packet
                       0x00, 0x01,
                       0x08, 0x00,
                       0x06,
                       0x04,
                       0x00, 0x01,
                       0x06,0x44,0x53,0x06,0x06,0x06, //our MAC address
                       0xc0, 0xa8, 0x02, 0x42,  //our IP address
                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  //MAC address of target 
                       0xc0, 0xa8, 0x02, 0x1E,   //IP addr of target (192.168.2.30 in our example)
                       
                       0x00,0x00,0x00,0x00,
                       0x00,0x00,0x00,0x00,
                       0x00,0x00,0x00,0x00,
                       0x00,0x00,0x00,0x00,
                       0x00,0x00,                 //18 bytes pad to get to minimum payload of 46
                       };                             

char ethpacket[ETH_PACKETSIZE];

#define NETIF_SEND_EP     0x05

int main(int argc, char *argv[])
{
	struct usb_device *dev;	
	struct usb_dev_handle *hdl;
	int i;

  printf("\ninitializing USB communication...");
	usb_init();
	usb_find_busses();                            
  usb_find_devices();
  printf("[SUCCESS].");
	
	dev = find_device(VENDOR_ID, PRODUCT_ID);
	if (dev == NULL) {
		printf("\nFATAL: lockdown verifier not found!");
		return -1;
	}
	printf("\nlockdown verifier found.");
	
	hdl = usb_open(dev);
	
	i = usb_set_configuration(hdl, 1);
	if (i < 0) {
		fprintf(stderr, "usb_set_configuration failed\n");
	}
  printf("\nlockdown verifier configuration selected.");
  
	                                     
	i = usb_claim_interface(hdl, 0);
	if (i < 0) {
		fprintf(stderr, "usb_claim_interface failed %d\n", i);
		return -1;
	}
  printf("\nclaimed lockdown USB interface.");

	memcpy(&ethpacket, &arpreqpacket, sizeof(arpreqpacket));
	
  {
   int j;
   unsigned int totalbytes=0;
   for(j=0; j < 1024; j++){
   
    //send the ARP request ethernet frame across the NETIF_SEND_EP
	 i = usb_bulk_write(hdl, NETIF_SEND_EP, (char *)&ethpacket, sizeof(ethpacket), 2000);
	 if (i < 0) {
	 	fprintf(stderr, "usb_bulk_write failed %d\n", i);
	 	return 0;
	 }
	 totalbytes+= sizeof(ethpacket);
	 
	 }
	 
	 printf("\ntransmitted %u bytes", totalbytes);
	}
  printf("\nwrote %u bytes successfully.", i);
	
	usb_release_interface(hdl, 0);
	usb_close(hdl);                             
	printf("\nclosed lockdown verifier USB communication.");

	return 0;
}


#elif defined(LDNVNET_DRV_COMM)
	UCHAR packetbuffer[1514];
	UCHAR rxpacketbuffer[1514];
	
  #define NETIF_SEND_EP     0x05
  #define NETIF_RECV_EP   0x84

  int ldnvf_read_packet(unsigned char *buffer, struct usb_dev_handle *hdl){
	 int i;
	 TMemoryCmd MemCmd;
	 unsigned int rxframesize;
	 
	 // send a vendor request to check if packet is available
	 MemCmd.dwAddress = 0x0;
	 MemCmd.dwLength = 0x0;
	 i = usb_control_msg(hdl, BM_REQUEST_TYPE, 0xF0, 0, 0, (char *)&MemCmd, sizeof(MemCmd), 1000);
	 if (i < 0){
		  printf("%s: usb_control_msg failed %d\n", __FUNCTION__, i);
		  return 0;		
	 }

   i = usb_bulk_read(hdl, NETIF_RECV_EP, (char *)&rxframesize, sizeof(rxframesize), 2000);
   if (i < 0) {
  		printf("%s:usb_bulk_read failed %d\n", __FUNCTION__, i);
  		return 0;
   }
 
   //if there is a packet we read it via the bulk
   if(rxframesize){
      	 i = usb_bulk_read(hdl, NETIF_RECV_EP, (char *)buffer, rxframesize, 2000);
	       if (i < 0) {
	 	       printf("\n%s: usb_bulk_read failed %d", __FUNCTION__, i);
	 	       return 0;
	       }
   }
 
 
   return rxframesize;
  }

	//ldnvnet driver communication test
	int main(int argc, char *argv[]){
		HANDLE drvh;
		DWORD bytes, rxbytes;
   	struct usb_device *dev;	
	  struct usb_dev_handle *hdl;
	  int i;
		 TMemoryCmd MemCmd;
	
		printf("\nOpening device...");
		drvh = CreateFile ( "\\\\.\\LDNVNET", 
								GENERIC_READ | GENERIC_WRITE,
								FILE_SHARE_READ,
								NULL,
								OPEN_EXISTING,
								FILE_ATTRIBUTE_NORMAL,
								NULL);
		if(drvh == INVALID_HANDLE_VALUE){
		  printf("\nFATAL: could not open handle to virtual ethernet driver!");
		  return -1;
		}	
			
		printf("\nOpened ldnvnet successfully.");

    //[USB initialization]
    printf("\ninitializing USB communication...");
	  usb_init();
	  usb_find_busses();                            
    usb_find_devices();
    printf("[SUCCESS].");
	
	  dev = find_device(VENDOR_ID, PRODUCT_ID);
	  if (dev == NULL) {
	  	printf("\nFATAL: lockdown verifier not found!");
		  return -1;
	  }  
	  printf("\nlockdown verifier found.");
	
	  hdl = usb_open(dev);
	
	  i = usb_set_configuration(hdl, 1);
	  if (i < 0) {
		 printf("\nFATAL: usb_set_configuration failed");
		 return -1;
	  }
    printf("\nlockdown verifier configuration selected.");
  
  	i = usb_claim_interface(hdl, 0);
	  if (i < 0) {
		  printf("\nFATAL: usb_claim_interface failed %d", i);
		  return -1;
	  }                                       
    printf("\nclaimed lockdown USB interface.");


    printf("\npress any key to quit...");
		while(!kbhit()){
			memset(packetbuffer, 0, sizeof(packetbuffer));
			memset(rxpacketbuffer, 0, sizeof(rxpacketbuffer));
			
      if(!DeviceIoControl(drvh, IOCTL_LDNVNET_READ_DATA,
					NULL, 0,
					&packetbuffer, sizeof(packetbuffer),
					&bytes, NULL)){
				printf("\nFATAL: could not send IOCTL!\n");
				return -1;
			}

			if(bytes){
    		int j;
				printf("\nTX: %u bytes successfully (dump follows):\n", bytes);
    		//for(j=0; j < bytes; j++)
    		//	printf("0x%02x ", packetbuffer[j]);
    		
    		 //first send a vendor request confirming size of TX packet
      	 MemCmd.dwAddress = 0x0;
      	 MemCmd.dwLength = bytes;
      	 i = usb_control_msg(hdl, BM_REQUEST_TYPE, 0xE0, 0, 0, (char *)&MemCmd, sizeof(MemCmd), 1000);
      	 if (i < 0){
      		  printf("%s: usb_control_msg failed %d\n", __FUNCTION__, i);
      		  return -1;		
      	 }
    		 
    		 //now write out the TX packet
      	 i = usb_bulk_write(hdl, NETIF_SEND_EP, (char *)&packetbuffer, bytes, 2000);
	       if (i < 0) {
	 	       printf("\nFATAL: usb_bulk_write failed %d", i);
	 	       return -1;
	       }
    	}
    	
    	
      //see if we have any RX packets to receive
      bytes=ldnvf_read_packet(&rxpacketbuffer, hdl);
      if(bytes){
        int j;
        printf("\nRX: %u bytes, dump follows:\n", bytes);
        //for(j=0; j < packetlength; j++)
    		//	printf("0x%02x ", packetbuffer[j]);
      
        if(!DeviceIoControl(drvh, IOCTL_LDNVNET_WRITE_DATA,
					&rxpacketbuffer, bytes,
					NULL, 0,
					&rxbytes, NULL)){
				printf("\nFATAL: could not send IOCTL!\n");
				return -1;
  			}

      
      }

    	
    	
    }
		
		CloseHandle(drvh);	
	
		return 0;
	}

#elif defined(USB_NETIF_READPACKET)
  #define NETIF_RECV_EP   0x84
  #define NETIF_SEND_EP   0x05
  

  int ldnvf_read_packet(unsigned char *buffer, struct usb_dev_handle *hdl){
	 int i;
	 TMemoryCmd MemCmd;
	 unsigned int rxframesize;
	 
	 // send a vendor request to check if packet is available
	 MemCmd.dwAddress = 0x0;
	 MemCmd.dwLength = 0x0;
	 i = usb_control_msg(hdl, BM_REQUEST_TYPE, 0xF0, 0, 0, (char *)&MemCmd, sizeof(MemCmd), 1000);
	 if (i < 0){
		  printf("%s: usb_control_msg failed %d\n", __FUNCTION__, i);
		  return 0;		
	 }

   i = usb_bulk_read(hdl, NETIF_RECV_EP, (char *)&rxframesize, sizeof(rxframesize), 2000);
   if (i < 0) {
  		printf("%s:usb_bulk_read failed %d\n", __FUNCTION__, i);
  		return 0;
   }
 
   //if there is a packet we read it via the bulk
   if(rxframesize){
      	 i = usb_bulk_read(hdl, NETIF_RECV_EP, (char *)buffer, rxframesize, 2000);
	       if (i < 0) {
	 	       printf("\n%s: usb_bulk_read failed %d", __FUNCTION__, i);
	 	       return 0;
	       }
   }
 
 
   return rxframesize;
  }


  //read packet from verifier test
  int main(int argc, char *argv[])
  { 
	 	struct usb_device *dev;	
	  struct usb_dev_handle *hdl;
	  int i;
   	 TMemoryCmd MemCmd;
		
    //[USB initialization]
    printf("\ninitializing USB communication...");
	  usb_init();
	  usb_find_busses();                            
    usb_find_devices();
    printf("[SUCCESS].");
	
	  dev = find_device(VENDOR_ID, PRODUCT_ID);
	  if (dev == NULL) {
	  	printf("\nFATAL: lockdown verifier not found!");
		  return -1;
	  }  
	  printf("\nlockdown verifier found.");
	
	  hdl = usb_open(dev);
	
	  i = usb_set_configuration(hdl, 1);
	  if (i < 0) {
		 printf("\nFATAL: usb_set_configuration failed");
		 return -1;
	  }
    printf("\nlockdown verifier configuration selected.");
  
  	i = usb_claim_interface(hdl, 0);
	  if (i < 0) {
		  printf("\nFATAL: usb_claim_interface failed %d", i);
		  return -1;
	  }                                       
    printf("\nclaimed lockdown USB interface.");

    printf("\nreading packets (any key to abort)...");
    fflush(stdin);
    while(!kbhit()){
      int packetlength, j;
      unsigned char packetbuffer[1514];  //max eth payload excluding FCS
            
      packetlength=ldnvf_read_packet(&packetbuffer, hdl);
      if(packetlength){
        printf("\nREAD packet, %u bytes, dump follows:\n", packetlength);
        for(j=0; j < packetlength; j++)
    			printf("0x%02x ", packetbuffer[j]);
      }
    
    }
    
  	usb_release_interface(hdl, 0);
	  usb_close(hdl);

	  return 0;
  }

#else
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
	if(!usbdevice_setdevicestate(hdl,RED_LED)){ //now force to trusted
		fprintf(stderr, "\nunable to set device state");
		return -1;
	}

	while(1){ 	//the main while loop we never exit

		printf("\nWaiting for lockdown device command...");
		while(!usbdevice_checkbuttonstatus(hdl))	
			;
		printf("\ngot button press");

		if(!CopyFile("e:\\grub\\grub_trusted_windows.conf", "e:\\grub\\grub.conf", FALSE)){
			printf("\nfailed to set destination environment!");
			exit(1);
		}
		
		SetSuspendState(TRUE, FALSE,FALSE);
	
		printf("\ngot awake...");

		//get state from vmm and set it
		if(!usbdevice_setdevicestate(hdl, RED_LED)){ //now force to trusted
			fprintf(stderr, "\nunable to set device state");
			return -1;
		}
	}

	usb_release_interface(hdl, 0);
	usb_close(hdl);

	return 0;
}

#endif

	

