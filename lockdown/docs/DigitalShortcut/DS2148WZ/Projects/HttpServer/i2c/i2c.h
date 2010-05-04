#ifndef _I2C_H_
#define _I2C_H_

#include "types.h"

//
//  Does not define slave RX statuses.  Bus errors (I2C_STAT == 0) is remapped
//  to I2CERR_ERROR in i2cStatus() so that we can use a value of 0 to indicate 
//  no error.
//
typedef enum
{
  I2CERR_NONE = 0,
  I2CERR_BUSY,
  I2CERR_EMPTY,
  I2CERR_TIMEOUT,
  I2CERR_TIMEOUTWC,
  I2CERR_TIMEOUTACKPOLL,
  I2CERR_NOTIMPLEMENTED,
  I2CERR_OTHER,
  I2CERR_BUSERROR,
  I2CERR_BUSERRORx       = 0x00,
  I2CERR_STARTTX         = 0x08,
  I2CERR_REPEATEDSTARTTX = 0x10,
  I2CERR_SLAWTX_ACKRX    = 0x18,
  I2CERR_SLAWTX_NACKRX   = 0x20,
  I2CERR_DATTX_ACKRX     = 0x28,
  I2CERR_DATTX_NACKRX    = 0x30,
  I2CERR_ARBLOST         = 0x38,
  I2CERR_SLARTX_ACKRX    = 0x40,
  I2CERR_SLARTX_NACKRX   = 0x48,
  I2CERR_DATRX_ACKTX     = 0x50,
  I2CERR_DATRX_NACKTX    = 0x58,
  I2CERR_NOINFO          = 0xf8
}
i2cErr_e;

//
//
extern i2cErr_e i2cErrno;

//
//
void i2cInit (void);
int i2cGetErrno (void);
const char *i2cStrerror (int err);
void i2cSetTimeout_o (unsigned int timeoutInMilliseconds);
int i2cWriteBuffer_o (uint8 address, uint8 *buffer, uint32 bufferLength);
int i2cReadBuffer_o (uint8 address, uint8 *buffer, uint32 bufferLength);
int i2cWriteReadBuffer_o (uint8 address, uint8 *buffer, uint32 putLength, uint32 getLength);
int i2cWriteBufferPoll (uint8 address, uint8 *buffer, uint32 bufferLength);
int i2cWriteReadBufferPoll (uint8 address, uint8 *buffer, uint32 putLength, uint32 getLength);

void i2cSetTimeout (int timeoutInMilliseconds);
int i2cWriteBuffer (uint8 address, uint8 *buffer, uint32 bufferLength);
int i2cReadBuffer (uint8 address, uint8 *buffer, uint32 bufferLength);
int i2cWriteReadBuffer (uint8 address, uint8 *buffer, uint32 putLength, uint32 getLength);

int eepromRead (uint16 addr, uint8 *buffer, int len);
int eepromWrite (uint16 addr, uint8 *buffer, int len);


#endif
