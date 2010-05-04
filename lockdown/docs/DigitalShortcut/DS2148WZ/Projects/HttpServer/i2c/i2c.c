//#include <stdio.h>

#include	"i2c.h"
#include	"../ARM2148/lpc21xx.h"
#include	"../ARM2148/processor.h"
#include	"../ARM2148/lpcI2C.h"

extern	uint32		miliSec;

extern	void	delay(unsigned long d);
extern	int 	printf(const char *format, ...);
extern	void	LogWr(uint16 data);

int i2cTransferBytes (uint8 address, uint8 *buffer, int bufferLenWrite, int bufferLenRead);
int i2cWriteBufferEx (uint8 address, uint8 *buffer, uint32 bufferLength, int milliseconds);
int i2cReadBufferEx (uint8 address, uint8 *buffer, uint32 bufferLength, int milliseconds);
int i2cWriteReadBufferEx (uint8 address, uint8 *buffer, uint32 putLength, uint32 getLength, int milliseconds);
int eepromRdSBlk (uint16 addr, uint8 *buffer, uint16 Length);
int eepromWrSBlk (uint16 addr, uint8 *buffer, uint16 Length);


//  Default timeout, in milliseconds for generic read/write
#define I2C_DEFAULT_TIMEOUT 100

volatile int i2cBusInUse;
uint8 i2cAddress;
uint8 *i2cDataBuffer;
int i2cDataLenWrite;
int i2cDataLenRead;
uint32 i2cTimeout = I2C_DEFAULT_TIMEOUT;
uint8 *i2cDataPtr;


int i2cWaitComplete (int milliseconds);


i2cErr_e i2cErrno;

//
//
//
typedef enum
{
  I2CFLAGS_START         = 0x0001,
  I2CFLAGS_REPEATEDSTART = 0x0002,
  I2CFLAGS_STOP          = 0x0004,
  I2CFLAGS_ADDRESS       = 0x0008,
  I2CFLAGS_WRITEDATA     = 0x0010,
  I2CFLAGS_READDATA      = 0x0020,
}
i2cFlags_e;

typedef enum
{
  I2CMODE_ACK = 0,
  I2CMODE_NACK,
  I2CMODE_READ
}
i2cMode_e;

static void i2cISR (void) __attribute__((naked));
static void i2cISR (void)
{
	ISR_ENTRY();
	
  i2cErrno = (I2C0_STAT & I2C_STAT_STATMASK);
	LogWr(0x49); LogWr(i2cErrno);

	switch (i2cErrno)  {
	//  Transmit conditions
	case I2CERR_BUSERRORx : // 0x00
		I2C0_CONSET = I2C_CONSET_STO | I2C_CONSET_AA;
		i2cBusInUse = 0;
		break;

	case I2CERR_STARTTX : // 0x08
		I2C0_DAT = i2cAddress;
		break;

	case I2CERR_REPEATEDSTARTTX : // 0x10
		I2C0_DAT = i2cAddress;
		break;

	case I2CERR_SLAWTX_ACKRX : // 0x18
		I2C0_DAT = *i2cDataPtr++;
		I2C0_CONCLR = I2C_CONCLR_STAC;
		break;

	case I2CERR_SLAWTX_NACKRX : // 0x20
		I2C0_CONSET = I2C_CONSET_STO;
		i2cBusInUse = 0;
		break;

	case I2CERR_DATTX_ACKRX : // 0x28
		if (--i2cDataLenWrite)  {
			I2C0_DAT = *i2cDataPtr++;
			I2C0_CONCLR = I2C_CONCLR_STAC;
		}
		else {
			if (!i2cDataLenRead) {
				I2C0_CONCLR = I2C_CONCLR_STAC;
				I2C0_CONSET = I2C_CONSET_STO;
				i2cBusInUse = 0;
			}
			else  {
				i2cAddress |= 0x01;
				i2cDataPtr = i2cDataBuffer;
				I2C0_CONSET = I2C_CONSET_STA;
			}
		}
		break;

	case I2CERR_DATTX_NACKRX : // 0x30
		I2C0_CONCLR = I2C_CONCLR_STAC;
		I2C0_CONSET = I2C_CONSET_STO;
		i2cBusInUse = 0;
		break;

	case I2CERR_ARBLOST : // 0x38
		I2C0_CONSET = I2C_CONSET_STA;
		break;

    //  Receive byte conditions
    //
	case I2CERR_SLARTX_ACKRX : // 0x40
		I2C0_CONCLR = I2C_CONCLR_STAC;
		I2C0_CONSET = I2C_CONSET_AA;
		break;

	case I2CERR_SLARTX_NACKRX : // 0x48
		I2C0_CONCLR = I2C_CONCLR_STAC;
		I2C0_CONSET = I2C_CONSET_STO;
		i2cBusInUse = 0;
		break;

	case I2CERR_DATRX_ACKTX : // 0x50
		*i2cDataPtr++ = I2C0_DAT;
		if (--i2cDataLenRead) {
			I2C0_CONCLR = I2C_CONCLR_STAC;
			I2C0_CONSET = I2C_CONSET_AA;
		} 
		else {
			I2C0_CONCLR = I2C_CONCLR_STAC | I2C_CONCLR_AAC;
			i2cBusInUse = 0;
		}
		break;

	case I2CERR_DATRX_NACKTX : // 0x58
		I2C0_CONCLR = I2C_CONCLR_STAC;
		I2C0_CONSET = I2C_CONSET_STO;
		i2cBusInUse = 0;
		break;

	case I2CERR_NOINFO :
		break;

	default:
		I2C0_CONCLR = I2C_CONCLR_I2ENC;
		i2cBusInUse = 0;
		break;
  }

  I2C0_CONCLR = I2C_CONSET_SI;
  
  VICVectAddr = 0;		// clear this interrupt from the VIC
  
	ISR_EXIT();                           // recover registers and return
  
}


//  Our PCLK is 60Mhz (12Mhz Xtal, PLL x 4, VBPDIV = /1), we want ~400KHz SCLK
void i2cInit (void)
{
  
	PCONP |= PCONP_PCI2C0;
	
	// setup SCL pin P02
	PINSEL0 &= ~(PINSEL0_P02_MASK );
	PINSEL0 |=   PINSEL0_P02_SCL0;
	
	// setup SDA pin P03
	PINSEL0 &= ~(PINSEL0_P03_MASK);
	PINSEL0 |=   PINSEL0_P03_SDA0;

	// set default bitrate of ~400KHz, empirical value + Users Manual p.147 
  I2C0_SCLL   = 76;
  I2C0_SCLH   = 76;

	// disable and reset interface
	I2C0_CONCLR = 0xFF;
	delay(10);

	// enable interface
  I2C0_CONCLR = I2C_CONCLR_MASK;
	I2C0_CONSET |= I2C_CONSET_I2EN;
	
  //  Initialize I2C0 interrupt
  VICIntSelect &= ~(1<<VIC_I2C0);					// setup I2C0 interrupt as IRQ
  VICVectCntl7 = VIC_ENABLE | VIC_I2C0;		// assign VIC slot
  VICVectAddr7 = (unsigned int)i2cISR;
	// enable I2C0 interrupt
	VICIntEnable |= (1<<VIC_I2C0);

}

//
//
//
static i2cErr_e i2cStatus (void)
{
  i2cErr_e status;

  while (!(I2C0_CONSET & I2C_CONSET_SI))
    ;

  if ((status = I2C0_STAT) == I2CERR_BUSERRORx)
    return I2CERR_BUSERROR;

  return status;
}

//
//
//
static i2cErr_e i2cStop (void)
{
  I2C0_CONCLR = I2C_CONCLR_SIC;
  I2C0_CONSET = I2C_CONSET_STO;

  while (I2C0_CONSET & I2C_CONSET_STO) ;

  return I2CERR_NONE;
}

//
//
//
static i2cErr_e i2cStart (void)
{
  I2C0_CONCLR = I2C_CONCLR_SIC;
  I2C0_CONSET = I2C_CONSET_STA;

  while (1)  {
    i2cErr_e status;

    if (((status = i2cStatus ()) == I2CERR_STARTTX) || (status == I2CERR_REPEATEDSTARTTX)) {
      I2C0_CONCLR = I2C_CONCLR_STAC;
      return I2CERR_NONE;
    }
    else if (status != I2CERR_NOINFO) {
      I2C0_CONCLR = I2C_CONCLR_STAC;
      return status;
    } else
      I2C0_CONCLR = I2C_CONCLR_SIC;
  }
}

//
//
//
static i2cErr_e i2cRepeatedStart (void)
{
  while (!(I2C0_CONSET & I2C_CONSET_SI)) ;

  I2C0_CONCLR = I2C_CONCLR_SIC;
  I2C0_CONSET = I2C_CONSET_STA;

  while (1) {
    i2cErr_e status;

    if (((status = i2cStatus ()) == I2CERR_STARTTX) || (status == I2CERR_REPEATEDSTARTTX)) {
      I2C0_CONCLR = I2C_CONCLR_STAC;
      return I2CERR_NONE;
    } 
    else if (status != I2CERR_NOINFO)  {
      I2C0_CONCLR = I2C_CONCLR_STAC;
      return status;
    }
    else
      I2C0_CONCLR = I2C_CONCLR_SIC;
  }
}

//
//
//
static i2cErr_e i2cPutByte (uint8 data)
{
  if (!(I2C0_CONSET & I2C_CONSET_SI))
    return I2CERR_BUSY;

  I2C0_DAT = data;
  I2C0_CONCLR = I2C_CONCLR_SIC;

  return I2CERR_NONE;
}

//
//
//
static i2cErr_e i2cGetByte (i2cMode_e mode, uint8 *pData)
{
  switch (mode)  {
    case I2CMODE_ACK :
      I2C0_CONCLR = I2C_CONCLR_SIC;
      I2C0_CONSET = I2C_CONSET_AA;
      break;

    case I2CMODE_NACK :
      I2C0_CONCLR = (I2C_CONCLR_AAC | I2C_CONCLR_SIC);
      break;

    case I2CMODE_READ :
      {
        if (!(I2C0_CONSET & I2C_CONSET_SI))
          return I2CERR_EMPTY;

        *pData = (uint8) I2C0_DAT;
      }
      break;
  }

  return I2CERR_NONE;
} 


static i2cErr_e i2cWriteBufferEx_o (uint8 address, uint8 *buffer, uint32 bufferLength, i2cFlags_e flags)
{
  uint32 i;
  i2cErr_e status;

  if (flags & I2CFLAGS_START) {
    if ((status = i2cStart ()) != I2CERR_NONE) {
      i2cStop ();
      return status;
    }
  }
  else if (flags & I2CFLAGS_REPEATEDSTART) {
    if ((status = i2cRepeatedStart ()) != I2CERR_NONE) {
      i2cStop ();
      return status;
    }
  }

  if (flags & I2CFLAGS_ADDRESS) {
    do
      if (((status = i2cPutByte (address & ~0x01)) != I2CERR_NONE) && (status != I2CERR_BUSY))
        return status;
    while (status == I2CERR_BUSY);
  }

  if (flags & I2CFLAGS_WRITEDATA) {
    for (i = 0; i < bufferLength; i++, buffer++) {
      while (1) {
        if (((status = i2cStatus ()) == I2CERR_SLAWTX_ACKRX) || (status == I2CERR_DATTX_ACKRX)) {
          do
            if (((status = i2cPutByte (*buffer)) != I2CERR_NONE) && (status != I2CERR_BUSY))
              return status;
          while (status == I2CERR_BUSY);
          break;
        }
        else if (status != I2CERR_NOINFO) {
          i2cStop ();
          return status;
        }
      }
    }
  }

  if (flags & I2CFLAGS_STOP) {
    while (1) {
      if (((status = i2cStatus ()) == I2CERR_SLAWTX_ACKRX) || (status == I2CERR_DATTX_ACKRX)) {
        i2cStop ();
        return I2CERR_NONE;
      }
      else if (status != I2CERR_NOINFO) {
        i2cStop ();
        return status;
      }
    }
  }
  return I2CERR_NONE;
}


static i2cErr_e i2cReadBufferEx_o (uint8 address, uint8 *buffer, uint32 bufferLength, i2cFlags_e flags)
{
  uint32 i;
  i2cErr_e status;

  if (flags & I2CFLAGS_START) {
    if ((status = i2cStart ()) != I2CERR_NONE) {
      i2cStop ();
      return status;
    }
  }
  else if (flags & I2CFLAGS_REPEATEDSTART) {
    if ((status = i2cRepeatedStart ()) != I2CERR_NONE) {
      i2cStop ();
      return status;
    }
  }

  if (flags & I2CFLAGS_ADDRESS) {
    do
      if (((status = i2cPutByte (address | 0x01)) != I2CERR_NONE) && (status != I2CERR_BUSY))
        return status;
    while (status == I2CERR_BUSY);
  }

  if (flags & I2CFLAGS_READDATA) {
    for (i = 0; i < bufferLength; i++, buffer++)  {
      while (1) {
        if (((status = i2cStatus ()) == I2CERR_SLARTX_ACKRX) || (status == I2CERR_SLARTX_NACKRX) || (status == I2CERR_DATRX_ACKTX))  {
          i2cGetByte ((i != bufferLength - 1) ? I2CMODE_ACK : I2CMODE_NACK, NULL);

          do
            status = i2cGetByte (I2CMODE_READ, buffer);
          while (status == I2CERR_EMPTY);

          break;
        }
        else if (status != I2CERR_NOINFO) {
          i2cStop ();
          return status;
        }
      }
    }
  }

  if (flags & I2CFLAGS_STOP)
    i2cStop ();

  return I2CERR_NONE;
}

//
//
static int i2cPoll (uint8 address)
{
  uint32 theFuture = miliSec + i2cTimeout;

  while (miliSec < theFuture)  {
    if ((i2cErrno = i2cStart ()) != I2CERR_NONE)
      break;
    if ((i2cErrno = i2cPutByte (address & ~0x01)) != I2CERR_NONE)
      break;
    if ((i2cErrno = i2cStatus ()) == I2CERR_SLAWTX_ACKRX)
      break;
  }

  if (i2cErrno != I2CERR_SLAWTX_ACKRX)
    i2cErrno = I2CERR_TIMEOUTACKPOLL;

  i2cStop ();

  if ( i2cErrno == I2CERR_SLAWTX_ACKRX ) return 0; else return -1;
}

//
void i2cSetTimeout_o (unsigned int timeoutInMilliseconds)
{
  i2cTimeout = timeoutInMilliseconds;
}

int i2cWriteBuffer_o (uint8 address, uint8 *buffer, uint32 bufferLength)
{
  if ((i2cErrno = i2cWriteBufferEx_o (address, buffer, bufferLength, I2CFLAGS_START | I2CFLAGS_ADDRESS | I2CFLAGS_WRITEDATA | I2CFLAGS_STOP)) != I2CERR_NONE) {
    return -1;
  }

  return 0;
}

int i2cReadBuffer_o (uint8 address, uint8 *buffer, uint32 bufferLength)
{
  if ((i2cErrno = i2cReadBufferEx_o (address, buffer, bufferLength, I2CFLAGS_START | I2CFLAGS_ADDRESS | I2CFLAGS_READDATA | I2CFLAGS_STOP)) != I2CERR_NONE) {
    return -1;
  }

  return 0;
}

int i2cWriteReadBuffer_o (uint8 address, uint8 *buffer, uint32 putLength, uint32 getLength)
{
  if ((i2cErrno = i2cWriteBufferEx_o (address, buffer, putLength, I2CFLAGS_START | I2CFLAGS_ADDRESS | I2CFLAGS_WRITEDATA)) != I2CERR_NONE) {
    return -1;
	}
	
  if ((i2cErrno = i2cReadBufferEx_o (address, buffer, getLength, I2CFLAGS_REPEATEDSTART | I2CFLAGS_ADDRESS | I2CFLAGS_READDATA | I2CFLAGS_STOP)) != I2CERR_NONE) {
    return -1;
  }
  
  return 0;
}

int i2cWriteBufferPoll (uint8 address, uint8 *buffer, uint32 bufferLength)
{
  int r;

  if (!(r = i2cWriteBuffer_o (address, buffer, bufferLength)))
    r = i2cPoll (address);

  return r;
}

int i2cWriteReadBufferPoll (uint8 address, uint8 *buffer, uint32 putLength, uint32 getLength)
{
  int r;

  if (!(r = i2cWriteReadBuffer_o (address, buffer, putLength, getLength)))
    r = i2cPoll (address);
    
  return r;
}

/*****************
 * I2C interrupt driven support
 *
*****************/
int i2cTransferBytes (uint8 address, uint8 *buffer, int bufferLenWrite, int bufferLenRead)
{
  //
  //  Determine if our first operation will be a write or read.  If both, the
  //  write always occurs first.
  //
  if (bufferLenWrite)
    address &= ~0x01;
  else if (bufferLenRead)
    address |= 0x01;
  else
  {
    i2cErrno = I2CERR_OTHER;
    return -1;
  }

  //
  //  Wait until last I2C operation has finished.  
  //
  if (i2cBusInUse && i2cWaitComplete (i2cTimeout))
  {
    i2cErrno = I2CERR_TIMEOUT;
    return -1;
  }

  //
  //  Mark bus as in use, save the address, buffer and length
  //
  i2cBusInUse = 1;
  i2cAddress = address;
  i2cDataBuffer = buffer;
  i2cDataLenWrite = bufferLenWrite;
  i2cDataLenRead = bufferLenRead;
  i2cDataPtr = buffer;

  I2C0_CONCLR = I2C_CONCLR_MASK;
  I2C0_CONSET = I2C_CONSET_I2EN;
  I2C0_CONSET = I2C_CONSET_STA;

  return 0;
}

//
//
//
int i2cWaitComplete (int milliseconds)
{
  if (i2cBusInUse)  {
    uint32 theFuture;

    if (milliseconds < 10) milliseconds = 10;

    for (theFuture = miliSec + (milliseconds / 10); i2cBusInUse; ) {
      if (miliSec > theFuture) {
        I2C0_CONCLR = I2C_CONCLR_I2ENC;
        i2cErrno = I2CERR_TIMEOUTWC;
        return -1;
      }
    }
  }

  return 0;
}

//
int i2cWriteBufferEx (uint8 address, uint8 *buffer, uint32 bufferLength, int milliseconds)
{
  if (i2cTransferBytes (address, buffer, bufferLength, 0))
    return -1;

  return i2cWaitComplete (milliseconds);
}

int i2cReadBufferEx (uint8 address, uint8 *buffer, uint32 bufferLength, int milliseconds)
{
  if (i2cTransferBytes (address, buffer, 0, bufferLength))
    return -1;

  return i2cWaitComplete (milliseconds);
}

int i2cWriteReadBufferEx (uint8 address, uint8 *buffer, uint32 putLength, uint32 getLength, int milliseconds)
{
  if (i2cTransferBytes (address, buffer, putLength, getLength))
    return -1;

  return i2cWaitComplete (milliseconds);
}

//
//  DANGER, WILL ROBINSON!  The callers buffer must persist until we're done
//
int i2cWriteBuffer (uint8 address, uint8 *buffer, uint32 bufferLength)
{
  return i2cWriteBufferEx (address, buffer, bufferLength, i2cTimeout);
}

int i2cReadBuffer (uint8 address, uint8 *buffer, uint32 bufferLength)
{
  return i2cReadBufferEx (address, buffer, bufferLength, i2cTimeout);
}

int i2cWriteReadBuffer (uint8 address, uint8 *buffer, uint32 putLength, uint32 getLength)
{
  return i2cWriteReadBufferEx (address, buffer, putLength, getLength, i2cTimeout);
}

void i2cSetTimeout (int timeoutInMilliseconds)
{
  if (timeoutInMilliseconds < 10)
    timeoutInMilliseconds = 10;

  i2cTimeout = timeoutInMilliseconds;
}


/*****************
 * EEProm CAT1640 8Kbx8 support
 *
*****************/

#define EEPROM_ADDRESS 0xae

// EEProm Read SubBlock in range 0xXX00-0xXX40
int eepromRdSBlk (uint16 addr, uint8 *buffer, uint16 Length)
{
  int r;
  
	addr &= 0x1fff;
  buffer [0] = addr >> 8;
  buffer [1] = addr;

  //r = i2cWriteReadBufferPoll ((uint8)EEPROM_ADDRESS, buffer, 2, Length);
  //printf("\n\reepromRdInt addr=%x len=%d", (int)addr, (int)Length);
	r = i2cWriteReadBuffer ((uint8)EEPROM_ADDRESS, buffer, 2, Length);
	
  return r;
}

// EEProm Write SubBlock in range 0xXX00-0xXX40
int eepromWrSBlk (uint16 addr, uint8 *buffer, uint16 Length)
{
  int r;

	addr &= 0x1fff;
  buffer [0] = addr >> 8;
  buffer [1] = addr;
  
  //r = i2cWriteBufferPoll ((uint8)EEPROM_ADDRESS, buffer, Length + 2);
  //printf("\n\reepromWrInt addr=%x len=%d", (int)addr, (int)Length);
	r = i2cWriteBuffer ((uint8)EEPROM_ADDRESS, buffer, Length + 2);
  return r;
}

int eepromWrite (uint16 addr, uint8* buffer, int Length)
{
	int len, bLen, el, r, idx;
	uint16 adr = addr;
	
	idx = 0;
	r = -1;
	len = Length;
	while ( len > 0 ) {
		if ( len > 64 ) bLen = 64; else bLen = len;
		el = ((adr|0x3f)-adr)+1;
		if ( el<bLen ) bLen = el;	
		r = eepromWrSBlk (adr, &buffer[idx], bLen);
		//printf("\n\reeWrBlk adr=%d(x%x) len=%d idx=%d r=%d ", adr, adr, bLen, idx, r);
		LogWr(0x50); LogWr(adr); LogWr((uint16)bLen);

		idx += bLen;
		len -= bLen;
		adr += bLen;
	}
	return r;
}

int eepromRead (uint16 addr, uint8* buffer, int Length)
{
	int bLen, len, el, r, idx;
	uint16 adr = addr;
	
	len = Length;
	if ( len > 500 ) len = 500;
	idx = 0;
	r = -1;
	
	while ( len > 0 ) {
		if ( len > 64 ) bLen = 64; else bLen = len;
		el = ((adr|0x3f)-adr)+1;
		if ( el<bLen ) bLen = el;	
		r = eepromRdSBlk (adr, &buffer[idx], bLen);
		//printf("\n\reeRdBlk adr=%d(x%x) len=%d idx=%d r=%d ", adr, adr, bLen, idx, r);
		LogWr(0x51); LogWr(adr); LogWr((uint16)bLen);

		idx += bLen;
		len -= bLen;
		adr += bLen;
	}
	return r;
}

