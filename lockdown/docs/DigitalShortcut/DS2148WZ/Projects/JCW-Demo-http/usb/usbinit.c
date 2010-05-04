//
//  $Id: usbinit.c 42 2008-10-04 18:40:36Z jcw $
//  $Revision: 42 $
//  $Author: jcw $
//  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/usb/usbinit.c $
//

#include "FreeRTOS.h"
#include "usbapi.h"


//
//  Data storage area for standard requests
//
static U8 abStdReqData [8];


//
//  USB reset handler
//
static void usbHandleReset(U8 bDevStatus __attribute__ ((unused)))
{
}

//
//
//
BOOL usbRegisterHandlers (void)
{
  usbHardwareInit ();
  usbHardwareRegisterDevIntHandler (usbHandleReset);
  usbHardwareRegisterEPIntHandler (0x00, usbHandleControlTransfer);
  usbHardwareRegisterEPIntHandler (0x80, usbHandleControlTransfer);
  usbRegisterRequestHandler (REQTYPE_TYPE_STANDARD, usbHandleStandardRequest, abStdReqData);

  return TRUE;
}
