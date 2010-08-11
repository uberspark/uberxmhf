//lockdown virtual ethernet driver IOCTL codes
//author: amit vasudevan (amitvasudevan@acm.org)

//note: this header MUST not contain any DDK specific macros
//or definitions as it is intended to be used by both the driver
//as well as the control application (ldnvfctl)

#define IOCTL_LDNVNET_TYPE	40000		//user-defined range

//note: IOCTL function codes from 0x800-0xFFF are for user-defined use
#define IOCTL_LDNVNET_READ_DATA \
    CTL_CODE (IOCTL_LDNVNET_TYPE, 0x900, METHOD_BUFFERED, FILE_READ_ACCESS)

#define IOCTL_LDNVNET_WRITE_DATA \
    CTL_CODE (IOCTL_LDNVNET_TYPE, 0x904, METHOD_BUFFERED, FILE_WRITE_ACCESS)



