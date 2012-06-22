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

//lockdown verifier monitor application for windows
// author: amit vasudevan (amitvasudevan@acm.org)

//-----------------------------
#include <windows.h>
#include <powrprof.h>
#include <stdio.h>
#include <conio.h>

#include "usb.h"
#include "public.h"

// types
#ifndef MIN
#define MIN(a,b)	((a)<(b)?(a):(b))
#endif
typedef unsigned int U32;
typedef unsigned char U8;

//#define SSLPA   1                 //define this to use SSL protocol analyzer
//#define LDNVNET	  1					//define this to use lockdown virtual network driver

#define MAX_TIME 3000

#define GREEN_LED     1
#define RED_LED       0

static unsigned char abData[16384];

//our verifier Vendor and Product ID
#define VENDOR_ID			0xFFFF
#define PRODUCT_ID		0x0004


#define BM_REQUEST_TYPE		(2<<5)

// this structure should match with the expectations of the 'custom' device!
typedef struct {
	U32		dwAddress;
	U32		dwLength;
} TMemoryCmd;


//forward prototypes
struct usb_dev_handle * ldn_find_verifier(void);

//set to 1 if we are operating in the trusted environment
int ldn_trusted_environment= 0;


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



//----------------------------------------------------------------------
//set device state (TRUSTED=1, UNTRUSTED=0)
//return 1 if success, 0 if failure
int usbdevice_setdevicestate(struct usb_dev_handle *hdl, int state){
	int i;
	TMemoryCmd MemCmd;

	// send a vendor request to check button status
	MemCmd.dwAddress = state; 
	MemCmd.dwLength = 0x0;
		
	i = usb_control_msg(hdl, BM_REQUEST_TYPE, 0xB0, 0, 0, (char *)&MemCmd, sizeof(MemCmd), 1000);

	if(i < 0)
		return 0; //usb_control_msg failed (verifier was removed?)
	else
		return 1;
}


//----------------------------------------------------------------------
//set lockdown verifier device state
void ldn_verifier_setstate(int state){
	struct usb_dev_handle *hdl;
	int status=0;
	
	do{
		while( (hdl = ldn_find_verifier()) == NULL)
			Sleep(100);	//discover our verifier

		status = usbdevice_setdevicestate(hdl, state);
			
		usb_release_interface(hdl, 0);
		usb_close(hdl);
		
	}while(!status);
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
		//fprintf(stderr, "usb_control_msg failed %d\n", i);
		return -1;		
	}

	//fprintf(stderr, "request success!\n");

	i = usb_bulk_read(hdl, 0x82, (char *)&buttonstatus, sizeof(buttonstatus), 2000);
	if (i < 0) {
		//fprintf(stderr, "usb_bulk_read failed %d\n", i);
		return -1;
	}

	if(buttonstatus){
		//printf("\nbutton press detected...");
		return 1;
	}


	return 0;
}


//----------------------------------------------------------------------
//check lockdown verifier button status
int ldn_verifier_checkbuttonstatus(void){
	struct usb_dev_handle *hdl;
	int status=-1;
	int verifier_was_unplugged=0;
	
	do{
		while( (hdl = ldn_find_verifier()) == NULL){
			verifier_was_unplugged=1;
			Sleep(100);	//discover our verifier
		}
		
		if(verifier_was_unplugged){
			verifier_was_unplugged=0;
			
			if(ldn_trusted_environment)
				usbdevice_setdevicestate(hdl, GREEN_LED); 
			else
				usbdevice_setdevicestate(hdl, RED_LED); 
		}
		
		status = usbdevice_checkbuttonstatus(hdl);
			
		usb_release_interface(hdl, 0);
		usb_close(hdl);
		
	}while(status < 0);
	
	return status;
}



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

//----------------------------------------------------------------------
struct usb_dev_handle * ldn_find_verifier(void){
	struct usb_device *dev;	
	struct usb_dev_handle *hdl;
	int i;
	
	//[USB initialization]
    //printf("\ninitializing USB communication...");
	usb_init();
	usb_find_busses();                            
    usb_find_devices();
    //printf("[SUCCESS].");
	
			
	dev = find_device(VENDOR_ID, PRODUCT_ID);
	if (dev == NULL) 
		return NULL;  //lockdown verifier not found!

    //printf("\nlockdown verifier found.");
	
	hdl = usb_open(dev);
	
	i = usb_set_configuration(hdl, 1);
	if (i < 0){
		usb_close(hdl);
		return NULL; //usb_set_configuration failed;
	}
    
    //printf("\nlockdown verifier configuration selected.");
  
  	i = usb_claim_interface(hdl, 0);
	if (i < 0) {
		usb_close(hdl);
		return NULL; //usb_claim_interface failed
	}                                       
    
    //printf("\nclaimed lockdown USB interface.");

	return hdl;
}



//======================================================================
//lockdown monitor main function
int main(int argc, char *argv[]){
	HANDLE drvh;
	DWORD bytes, rxbytes;
	int i;
	TMemoryCmd MemCmd;

	if(argc < 2){
		printf("\ninsufficient arguments: specify either 'true' or 'unte'");
		exit(0);
	}

	if(!strcmp(argv[1], "true"))
		ldn_trusted_environment=1;
	else
		ldn_trusted_environment=0;
	
	
	if(ldn_trusted_environment){
		#if defined (LDNVNET)	
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
		#endif
	}

    
	if(ldn_trusted_environment){
		#if defined(LDNVNET)
			#if defined(SSLPA)
			//initialize sslpa
			ssl_pa_init();
			#endif
		#endif  
	}

    //printf("\npress any key to quit...");
	while(1){
		printf("\nWaiting for lockdown device command...");

		//set the LED for this environment
		if(ldn_trusted_environment)
			ldn_verifier_setstate(GREEN_LED); 
		else
			ldn_verifier_setstate(RED_LED); 


		while(!ldn_verifier_checkbuttonstatus()){
			if(ldn_trusted_environment){
				#if defined (LDNVNET)
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
						//printf("\nTX: %u bytes successfully (dump follows):\n", bytes);
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

						//pass packet through analyzer
						#if defined(SSLPA)
						ssl_pa_analyze((unsigned char *)&packetbuffer, bytes);
						#endif
						 
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
						//printf("\nRX: %u bytes, dump follows:\n", bytes);
						//for(j=0; j < packetlength; j++)
						//	printf("0x%02x ", packetbuffer[j]);

						//pass packet through analyzer
						#if defined(SSLPA)
						ssl_pa_analyze((unsigned char *)&rxpacketbuffer, bytes);
						#endif


						if(!DeviceIoControl(drvh, IOCTL_LDNVNET_WRITE_DATA,
								&rxpacketbuffer, bytes,
								NULL, 0,
								&rxbytes, NULL)){
							printf("\nFATAL: could not send IOCTL!\n");
							return -1;
						}
					}
				#endif // LDNVNET
			}
		}	
			
		printf("\ngot button press");

		if(ldn_trusted_environment){
			if(!CopyFile("e:\\grub\\menu_ue.lst", "e:\\grub\\menu.lst", FALSE)){
				printf("\nfailed to set destination environment!");
				exit(1);
			}
		}else{
			if(!CopyFile("e:\\grub\\menu_te.lst", "e:\\grub\\menu.lst", FALSE)){
				printf("\nfailed to set destination environment!");
				exit(1);
			}
		}
			
      	SetSuspendState(TRUE, FALSE,FALSE);
      	
      	printf("\ngot awake...");
	}


	if(ldn_trusted_environment){
		#if defined (LDNVNET)		
		CloseHandle(drvh);	
		#endif
	}

	
	return 0;
}
	

