//
//  $Id: spi.c 81 2008-10-06 01:51:15Z jcw $
//  $Revision: 81 $
//  $Author: jcw $
//  $Date: 2008-10-05 21:51:15 -0400 (Sun, 05 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/mmc/spi.c $
//

#include "lpc210x.h"
#include "spi.h"

//
//  Some macros to make it more obvious...
//
#define WAIT_TXFIFO_NOTFULL() do { while (!(SSP_SR & SSP_SR_TNF)); } while (0)
#define WAIT_RXFIFO_NOTEMPTY() do { while (!(SSP_SR & SSP_SR_RNE)); } while (0)
#define WAIT_SSP_IDLE() do { while (SSP_SR & SSP_SR_BSY); } while (0)

/*************************************************************************
 *
 *    Used with ICCARM and AARM.
 *
 *    (c) Copyright IAR Systems 2003
 *
 *    File name   : mmc_ll.h
 *    Description : define MMC module
 *
 *    History :
 *    1. Data        : July 1, 2005
 *       Author      : Stanimir Bonev
 *       Description : Create
 *    2. Data        : July 1, 2005
 *       Author      : Stanimir Bonev
 *       Description : Modify
 *        Fix a lock problem in spiReceiveBlock
 *
 *    $Revision: 81 $
 * (C) Joel Winarske, 2006,2007                                        
**************************************************************************/

//
//  Return 1 if MMC card present, 0 if not
//
inline int spiHardwareCardPresent (void)
{
  return (GPIO1_FIOPIN & GPIO_IO_P25) ? 0 : 1;
}

//
//  Return 1 if card write protected (or not present), 0 if not write protected
//
inline int spiHardwareWriteProtected (void)
{
  if (!spiHardwareCardPresent ())
    return 1;

  return (GPIO1_FIOPIN & GPIO_IO_P24) ? 1 : 0;
}

/*************************************************************************
 * Function Name: spiChipSelect
 * Parameters: Boolean Select
 * Return: none
 *
 * Description: MMC Chip select control
 * Select = true  - Chip is enabled
 * Select = false - Chip is disabled
 *
 *************************************************************************/
void spiChipSelect (BOOL select)
{
  if (select)
    GPIO0_FIOCLR = GPIO_IO_P20;
  else
  {
    GPIO0_FIOSET = GPIO_IO_P20;
    WAIT_TXFIFO_NOTFULL ();
    SSP_DR = 0xff;

    //
    //  Wait until TX fifo and TX shift buffer are empty, discard any received data
    //
    WAIT_SSP_IDLE ();
    WAIT_RXFIFO_NOTEMPTY ();

    do
    {
      select = SSP_DR;
    }
    while (SSP_SR & SSP_SR_RNE);
  }
}

/*************************************************************************
 * Function Name: spiSetClockFreq
 * Parameters: Int32U Frequency
 * Return: Int32U
 *
 * Description: Set SPI ckl frequency
 *
 *************************************************************************/
U32 spiSetClockFreq (U32 frequency)
{
  U32 div = SYSTEMPERIPHERIALCLOCK / frequency;

  if (div < 2)
    div = 2;
  else if (div > 254)
    div = 254;

  ++div; 
  div &= ~1;
  SSP_CPSR = div;

  return (SYSTEMPERIPHERIALCLOCK / div);
}

/*************************************************************************
 * Function Name: spiInit
 * Parameters: none
 * Return: none
 *
 * Description: Init SPI, Card Present, Write Protect and Chip select pins
 *
 *************************************************************************/
void spiInit (void)
{
  U32 i;
  volatile U32 dummy;

  //
  //  P0.20 as chip select (output), P1.25 as card present (input), and P1.24 as write protect (input)
  //
  GPIO0_FIOSET  = GPIO_IO_P20;
  GPIO0_FIODIR |= GPIO_IO_P20;
  GPIO1_FIODIR &= ~(GPIO_IO_P25 | GPIO_IO_P24);

  //
  //  SPI init
  //
  SCB_PCONP |= SCB_PCONP_PCSPI1;

  SSP_CR0  = SSP_CR0_DSS_8 | SSP_CR0_FRF_SPI;
  SSP_CR1  = 0x00;
  SSP_IMSC = 0x00;

  //
  //  Clock Freq. Identification Mode < 400kHz
  //
  spiSetClockFreq (400000);

  PCB_PINSEL1 |=  PCB_PINSEL1_P017_SCK1;
  PCB_PINSEL1 |=  PCB_PINSEL1_P018_MISO1;
  PCB_PINSEL1 |=  PCB_PINSEL1_P019_MOSI1;
  PCB_PINSEL1 &= ~PCB_PINSEL1_P020_MASK;

  //
  //  Enable SPI
  //
  SSP_CR1 |= SSP_CR1_SSE;

  for (i = 0; i < 8; i++)
    dummy = SSP_DR;
}

/*************************************************************************
 * Function Name: spiTransferByte
 * Parameters: U8 ch
 * Return: U8
 *
 * Description: Read byte from SPI
 *
 *************************************************************************/
U8 spiTransferByte (U8 c)
{
  WAIT_TXFIFO_NOTFULL ();

  SSP_DR = c;

  WAIT_RXFIFO_NOTEMPTY ();

  return SSP_DR;
}

/*-----------------------------------------------------------------------*/
/* Wait for card ready                                                   */
/*-----------------------------------------------------------------------*/
U8 spiWaitReady (void)
{
  U8 res;

  // 
  // TODO: add in 500ms timeout
  //
  do
  {      
    SSP_DR = 0xff;

    WAIT_RXFIFO_NOTEMPTY ();

    res = SSP_DR;
  }
  while (res != 0xff);

  return res;
}

/*************************************************************************
 * Function Name: spiSendBlock
 * Parameters: pInt8U pData, Int32U Size
 *
 * Return: void
 *
 * Description: Read byte from SPI
 *
 *************************************************************************/
void spiSendBlock (const U8 *pData, U32 size)
{
  //
  //  Change submitted by David Johnson
  //
  volatile U32 dummy;

  while (size--)
  {
    WAIT_TXFIFO_NOTFULL ();

    SSP_DR = *pData++;
    
    WAIT_RXFIFO_NOTEMPTY ();

    dummy = SSP_DR;
  }
}

/*************************************************************************
 * Function Name: spiReceiveBlock
 * Parameters: pInt8U pData, Int32U Size
 *
 * Return: void
 *
 * Description: Read byte from SPI
 *
 *************************************************************************/
void spiReceiveBlock (U8 *pData, U32 size)
{
  U32 delta = 0;

  while (size || delta)
  {
    while ((SSP_SR & SSP_SR_TNF) && (delta < SSP_FIFO_DEPTH) && size)
    {
      SSP_DR = 0xff;
      --size; 
      ++delta;
    }

    while (SSP_SR & SSP_SR_RNE)
    {
      *pData++ = SSP_DR;
      --delta;
    }
  }
}

/*************************************************************************
 * Function Name: spiDly_1ms
 * Parameters: Int32U Delay
 * Return: none
 *
 * Description: Delay [msec]
 *
 *************************************************************************/
void spiDelay1ms (U32 delay)
{
  volatile U32 i;

  for (;delay; --delay)
  {
    for (i = SPI_DLY_1MSEC; i; --i)
      ;
  }
}
