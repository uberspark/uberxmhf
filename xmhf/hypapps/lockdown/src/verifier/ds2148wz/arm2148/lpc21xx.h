/*-
 ******************************************************************************
 *
 * $RCSfile: $
 * $Revision: $
 *
 * Header file for Philips LPC21xx ARM Processors 
 * Copyright 2004 R O SoftWare
 *
 * No guarantees, warrantees, or promises, implied or otherwise.
 * May be used for hobby or commercial purposes provided copyright
 * notice remains intact.
 *
 *****************************************************************************/
#ifndef INC_LPC21xx_H
#define INC_LPC21xx_H

#define REG_8           volatile unsigned char
#define REG16           volatile unsigned short
#define REG32           volatile unsigned long


#define iap_entry ((IAP) 0x7FFFFFF1)            // IAP entry point

#include "lpcGPIO.h"
#include "lpcVIC.h"
#include "lpcUART.h"
#include "lpcSCB.h"
#include "lpcTMR.h"


///////////////////////////////////////////////////////////////////////////////
// Watchdog
#define WD              ((wdRegs_t *)0xE0000000)

// Watchdog Registers
#define WDMOD           WD->mod         /* Watchdog Mode Register */
#define WDTC            WD->tc          /* Watchdog Time Constant Register */
#define WDFEED          WD->feed        /* Watchdog Feed Register */
#define WDTV            WD->tv          /* Watchdog Time Value Register */

///////////////////////////////////////////////////////////////////////////////
// Timer 0
#define TMR0            ((pwmTmrRegs_t *)0xE0004000)

// Timer 0 Registers
#define T0IR            TMR0->ir        /* Interrupt Register */
#define T0TCR           TMR0->tcr       /* Timer Control Register */
#define T0TC            TMR0->tc        /* Timer Counter */
#define T0PR            TMR0->pr        /* Prescale Register */
#define T0PC            TMR0->pc        /* Prescale Counter Register */
#define T0MCR           TMR0->mcr       /* Match Control Register */
#define T0MR0           TMR0->mr0       /* Match Register 0 */
#define T0MR1           TMR0->mr1       /* Match Register 1 */
#define T0MR2           TMR0->mr2       /* Match Register 2 */
#define T0MR3           TMR0->mr3       /* Match Register 3 */
#define T0CCR           TMR0->ccr       /* Capture Control Register */
#define T0CR0           TMR0->cr0       /* Capture Register 0 */
#define T0CR1           TMR0->cr1       /* Capture Register 1 */
#define T0CR2           TMR0->cr2       /* Capture Register 2 */
#define T0CR3           TMR0->cr3       /* Capture Register 3 */
#define T0EMR           TMR0->emr       /* External Match Register */

///////////////////////////////////////////////////////////////////////////////
// Timer 1
#define TMR1            ((pwmTmrRegs_t *)0xE0008000)

// Timer 1 Registers
#define T1IR            TMR1->ir        /* Interrupt Register */
#define T1TCR           TMR1->tcr       /* Timer Control Register */
#define T1TC            TMR1->tc        /* Timer Counter */
#define T1PR            TMR1->pr        /* Prescale Register */
#define T1PC            TMR1->pc        /* Prescale Counter Register */
#define T1MCR           TMR1->mcr       /* Match Control Register */
#define T1MR0           TMR1->mr0       /* Match Register 0 */
#define T1MR1           TMR1->mr1       /* Match Register 1 */
#define T1MR2           TMR1->mr2       /* Match Register 2 */
#define T1MR3           TMR1->mr3       /* Match Register 3 */
#define T1CCR           TMR1->ccr       /* Capture Control Register */
#define T1CR0           TMR1->cr0       /* Capture Register 0 */
#define T1CR1           TMR1->cr1       /* Capture Register 1 */
#define T1CR2           TMR1->cr2       /* Capture Register 2 */
#define T1CR3           TMR1->cr3       /* Capture Register 3 */
#define T1EMR           TMR1->emr       /* External Match Register */

///////////////////////////////////////////////////////////////////////////////
// Pulse Width Modulator (PWM)
#define PWM             ((pwmTmrRegs_t *)0xE0014000)

// PWM Registers
#define PWMIR           PWM->ir         /* Interrupt Register */
#define PWMTCR          PWM->tcr        /* Timer Control Register */
#define PWMTC           PWM->tc         /* Timer Counter */
#define PWMPR           PWM->pr         /* Prescale Register */
#define PWMPC           PWM->pc         /* Prescale Counter Register */
#define PWMMCR          PWM->mcr        /* Match Control Register */
#define PWMMR0          PWM->mr0        /* Match Register 0 */
#define PWMMR1          PWM->mr1        /* Match Register 1 */
#define PWMMR2          PWM->mr2        /* Match Register 2 */
#define PWMMR3          PWM->mr3        /* Match Register 3 */
#define PWMMR4          PWM->mr4        /* Match Register 4 */
#define PWMMR5          PWM->mr5        /* Match Register 5 */
#define PWMMR6          PWM->mr6        /* Match Register 6 */
#define PWMPCR          PWM->pcr        /* Control Register */
#define PWMLER          PWM->ler        /* Latch Enable Register */

///////////////////////////////////////////////////////////////////////////////
// Universal Asynchronous Receiver Transmitter 0 (UART0)
#define UART0           ((uartRegs_t *)0xE000C000)
#define U0_PINSEL       (0x00000005)    /* PINSEL0 Value for UART0 */
#define U0_PINMASK      (0x0000000F)    /* PINSEL0 Mask for UART0 */

// UART0 Registers
#define U0RBR           UART0->rbr      /* Receive Buffer Register */
#define U0THR           UART0->thr      /* Transmit Holding Register */
#define U0IER           UART0->ier      /* Interrupt Enable Register */
#define U0IIR           UART0->iir      /* Interrupt ID Register */
#define U0FCR           UART0->fcr      /* FIFO Control Register */
#define U0LCR           UART0->lcr      /* Line Control Register */
#define U0LSR           UART0->lsr      /* Line Status Register */
#define U0SCR           UART0->scr      /* Scratch Pad Register */
#define U0DLL           UART0->dll      /* Divisor Latch Register (LSB) */
#define U0DLM           UART0->dlm      /* Divisor Latch Register (MSB) */

///////////////////////////////////////////////////////////////////////////////
// Universal Asynchronous Receiver Transmitter 1 (UART1)
#define UART1           ((uartRegs_t *)0xE0010000)
#define U1_PINSEL       (0x00050000)    /* PINSEL0 Value for UART1 */
#define U1_PINMASK      (0x000F0000)    /* PINSEL0 Mask for UART1 */

// UART1 Registers
#define U1RBR           UART1->rbr      /* Receive Buffer Register */
#define U1THR           UART1->thr      /* Transmit Holding Register */
#define U1IER           UART1->ier      /* Interrupt Enable Register */
#define U1IIR           UART1->iir      /* Interrupt ID Register */
#define U1FCR           UART1->fcr      /* FIFO Control Register */
#define U1LCR           UART1->lcr      /* Line Control Register */
#define U1MCR           UART1->mcr      /* MODEM Control Register */
#define U1LSR           UART1->lsr      /* Line Status Register */
#define U1MSR           UART1->msr      /* MODEM Status Register */
#define U1SCR           UART1->scr      /* Scratch Pad Register */
#define U1DLL           UART1->dll      /* Divisor Latch Register (LSB) */
#define U1DLM           UART1->dlm      /* Divisor Latch Register (MSB) */

///////////////////////////////////////////////////////////////////////////////
// I2C Interface
#define I2C             ((i2cRegs_t *)0xE001C000)

// I2C Registers
#define I2C0_CONSET        I2C->conset     /* Control Set Register */
#define I2C0_STAT          I2C->stat       /* Status Register */
#define I2C0_DAT           I2C->dat        /* Data Register */
#define I2C0_ADR           I2C->adr        /* Slave Address Register */
#define I2C0_SCLH          I2C->sclh       /* SCL Duty Cycle Register (high half word) */
#define I2C0_SCLL          I2C->scll       /* SCL Duty Cycle Register (low half word) */
#define I2C0_CONCLR        I2C->conclr     /* Control Clear Register */

#define I2C_CONSET_AA       (0x00000004)
#define I2C_CONSET_SI       (0x00000008)
#define I2C_CONSET_STO      (0x00000010)
#define I2C_CONSET_STA      (0x00000020)
#define I2C_CONSET_I2EN     (0x00000040)
#define I2C_CONSET_MASK     (0x0000007c)

#define I2C_STAT_STATMASK   (0x000000f8)
#define I2C_STAT_STATSHIFT  (3)

#define I2C_ADDR_GC         (0x00000001)
#define I2C_ADDR_ADDRMASK   (0x000000fe)
#define I2C_ADDR_ADDRSHIFT  (1)

#define I2C_CONCLR_AAC      (0x00000004)
#define I2C_CONCLR_SIC      (0x00000008)
#define I2C_CONCLR_STAC     (0x00000020)
#define I2C_CONCLR_I2ENC    (0x00000040)
#define I2C_CONCLR_MASK     (0x0000006c)



///////////////////////////////////////////////////////////////////////////////
// Serial Peripheral Interface 0 (SPI0)
#define SPI0            ((spiRegs_t *)0xE0020000)

// SPI0 Registers
#define S0SPCR          SPI0->cr        /* Control Register */
#define S0SPSR          SPI0->sr        /* Status Register */
#define S0SPDR          SPI0->dr        /* Data Register */
#define S0SPCCR         SPI0->ccr       /* Clock Counter Register */
#define S0SPINT         SPI0->flag      /* Interrupt Flag Register */


/*##############################################################################
## SSP - Synchronous Serial Port
##############################################################################*/

#define SSP_CR0         *(volatile unsigned int *)0xe0068000
#define SSP_CR1         *(volatile unsigned int *)0xe0068004
#define SSP_DR          *(volatile unsigned int *)0xe0068008
#define SSP_SR          *(volatile unsigned int *)0xe006800C
#define SSP_CPSR        *(volatile unsigned int *)0xe0068010
#define SSP_IMSC        *(volatile unsigned int *)0xe0068014
#define SSP_RIS         *(volatile unsigned int *)0xe0068018
#define SSP_MIS         *(volatile unsigned int *)0xe006801C
#define SSP_ICR         *(volatile unsigned int *)0xe0068020

#define SSP_FIFO_DEPTH  (8)

#define SSP_CR0_DSS_4   ((unsigned int) 0x00000003)
#define SSP_CR0_DSS_5   ((unsigned int) 0x00000004)
#define SSP_CR0_DSS_6   ((unsigned int) 0x00000005)
#define SSP_CR0_DSS_7   ((unsigned int) 0x00000006)
#define SSP_CR0_DSS_8   ((unsigned int) 0x00000007)
#define SSP_CR0_DSS_9   ((unsigned int) 0x00000008)
#define SSP_CR0_DSS 10  ((unsigned int) 0x00000009)
#define SSP_CR0_DSS_11  ((unsigned int) 0x0000000a)
#define SSP_CR0_DSS_12  ((unsigned int) 0x0000000b)
#define SSP_CR0_DSS_13  ((unsigned int) 0x0000000c)
#define SSP_CR0_DSS_14  ((unsigned int) 0x0000000d)
#define SSP_CR0_DSS_15  ((unsigned int) 0x0000000e)
#define SSP_CR0_DSS_16  ((unsigned int) 0x0000000f)
#define SSP_CR0_FRF_SPI ((unsigned int) 0x00000000)
#define SSP_CR0_FRF_SSI ((unsigned int) 0x00000010)
#define SSP_CR0_FRF_MW  ((unsigned int) 0x00000020)
#define SSP_CR0_CPOL    ((unsigned int) 0x00000040)
#define SSP_CR0_CPHA    ((unsigned int) 0x00000080)
#define SSP_CR0_SCR     ((unsigned int) 0x0000ff00)

#define SSP_CR1_LBM     ((unsigned int) 0x00000001)
#define SSP_CR1_SSE     ((unsigned int) 0x00000002)
#define SSP_CR1_MS      ((unsigned int) 0x00000004)
#define SSP_CR1_SOD     ((unsigned int) 0x00000008)

#define SSP_SR_TFE      ((unsigned int) 0x00000001)
#define SSP_SR_TNF      ((unsigned int) 0x00000002)
#define SSP_SR_RNE      ((unsigned int) 0x00000004)
#define SSP_SR_RFF      ((unsigned int) 0x00000008)
#define SSP_SR_BSY      ((unsigned int) 0x00000010)

#define SSP_IMSC_RORIM  ((unsigned int) 0x00000001)
#define SSP_IMSC_RTIM   ((unsigned int) 0x00000002)
#define SSP_IMSC_RXIM   ((unsigned int) 0x00000004)
#define SSP_IMSC_TXIM   ((unsigned int) 0x00000008)

#define SSP_RIS_RORRIS  ((unsigned int) 0x00000001)
#define SSP_RIS_RTRIS   ((unsigned int) 0x00000002)
#define SSP_RIS_RXRIS   ((unsigned int) 0x00000004)
#define SSP_RIS_TXRIS   ((unsigned int) 0x00000008)

#define SSP_MIS_RORMIS  ((unsigned int) 0x00000001)
#define SSP_MIS_RTMIS   ((unsigned int) 0x00000002)
#define SSP_MIS_RXMIS   ((unsigned int) 0x00000004)
#define SSP_MIS_TXMIS   ((unsigned int) 0x00000008)

#define SSP_ICR_RORIC   ((unsigned int) 0x00000001)
#define SSP_ICR_RTIC    ((unsigned int) 0x00000002)


///////////////////////////////////////////////////////////////////////////////
// Real Time Clock
#define RTC             ((rtcRegs_t *)0xE0024000)

// RTC Registers
#define RTCILR          RTC->ilr        /* Interrupt Location Register */
#define RTCCTC          RTC->ctc        /* Clock Tick Counter */
#define RTCCCR          RTC->ccr        /* Clock Control Register */
#define RTCCIIR         RTC->ciir       /* Counter Increment Interrupt Register */
#define RTCAMR          RTC->amr        /* Alarm Mask Register */
#define RTCCTIME0       RTC->ctime0     /* Consolidated Time Register 0 */
#define RTCCTIME1       RTC->ctime1     /* Consolidated Time Register 1 */
#define RTCCTIME2       RTC->ctime2     /* Consolidated Time Register 2 */
#define RTCSEC          RTC->sec        /* Seconds Register */
#define RTCMIN          RTC->min        /* Minutes Register */
#define RTCHOUR         RTC->hour       /* Hours Register */
#define RTCDOM          RTC->dom        /* Day Of Month Register */
#define RTCDOW          RTC->dow        /* Day Of Week Register */
#define RTCDOY          RTC->doy        /* Day Of Year Register */
#define RTCMONTH        RTC->month      /* Months Register */
#define RTCYEAR         RTC->year       /* Years Register */
#define RTCALSEC        RTC->alsec      /* Alarm Seconds Register */
#define RTCALMIN        RTC->almin      /* Alarm Minutes Register */
#define RTCALHOUR       RTC->alhour     /* Alarm Hours Register */
#define RTCALDOM        RTC->aldom      /* Alarm Day Of Month Register */
#define RTCALDOW        RTC->aldow      /* Alarm Day Of Week Register */
#define RTCALDOY        RTC->aldoy      /* Alarm Day Of Year Register */
#define RTCALMON        RTC->almon      /* Alarm Months Register */
#define RTCALYEAR       RTC->alyear     /* Alarm Years Register */
#define RTCPREINT       RTC->preint     /* Prescale Value Register (integer) */
#define RTCPREFRAC      RTC->prefrac    /* Prescale Value Register (fraction) */

#define ILR_RTCCIF  ((unsigned int) 0x00000001)
#define ILR_RTCALF  ((unsigned int) 0x00000002)
#define ILR_MASK    ((unsigned int) 0x00000003)

#define CCR_CLKEN   ((unsigned int) 0x00000001)
#define CCR_CTCRST  ((unsigned int) 0x00000002)
#define CCR_TEST    ((unsigned int) 0x0000000c)
#define CCR_CLKSRC  ((unsigned int) 0x00000010)

#define CIIR_IMSEC  ((unsigned int) 0x00000001)
#define CIIR_IMMIN  ((unsigned int) 0x00000002)
#define CIIR_IMHOUR ((unsigned int) 0x00000004)
#define CIIR_IMDOM  ((unsigned int) 0x00000008)
#define CIIR_IMDOW  ((unsigned int) 0x00000010)
#define CIIR_IMDOY  ((unsigned int) 0x00000020)
#define CIIR_IMMON  ((unsigned int) 0x00000040)
#define CIIR_IMYEAR ((unsigned int) 0x00000080)
#define CIIR_IMMASK ((unsigned int) 0x000000ff)

#define AMR_AMRSEC  ((unsigned int) 0x00000001)
#define AMR_AMRMIN  ((unsigned int) 0x00000002)
#define AMR_AMRHOUR ((unsigned int) 0x00000004)
#define AMR_AMRDOM  ((unsigned int) 0x00000008)
#define AMR_AMRDOW  ((unsigned int) 0x00000010)
#define AMR_AMRDOY  ((unsigned int) 0x00000020)
#define AMR_AMRMON  ((unsigned int) 0x00000040)
#define AMR_AMRYEAR ((unsigned int) 0x00000080)
#define AMR_AMRMASK ((unsigned int) 0x000000ff)


///////////////////////////////////////////////////////////////////////////////
// General Purpose Input/Output
#define GPIO            ((gpioRegs_t *)0xE0028000)

// GPIO Registers
#define IO0PIN          GPIO->in0       /* P0 Pin Value Register */
#define IO0SET          GPIO->set0      /* P0 Pin Output Set Register */
#define IO0DIR          GPIO->dir0      /* P0 Pin Direction Register */
#define IO0CLR          GPIO->clr0      /* P0 Pin Output Clear Register */
#define IO1PIN          GPIO->in1       /* P1 Pin Value Register */
#define IO1SET          GPIO->set1      /* P1 Pin Output Set Register */
#define IO1DIR          GPIO->dir1      /* P1 Pin Direction Register */
#define IO1CLR          GPIO->clr1      /* P1 Pin Output Clear Register */

///////////////////////////////////////////////////////////////////////////////
// Pin Connect Block
#define PINSEL          ((pinRegs_t *)0xE002C000)

// Pin Connect Block Registers
#define PINSEL0         PINSEL->sel0    /* Pin Function Select Register 0 */
#define PINSEL1         PINSEL->sel1    /* Pin Function Select Register 1 */
#define PINSEL2         PINSEL->sel2    /* Pin Function Select Register 2 */

#define PINSEL0_P00_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P00_TXD0      ((unsigned int) 0x00000001)
#define PINSEL0_P00_PWM1      ((unsigned int) 0x00000002)
#define PINSEL0_P00_RSVD3     ((unsigned int) 0x00000003)
#define PINSEL0_P00_MASK      ((unsigned int) 0x00000003)

#define PINSEL0_P01_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P01_RXD0      ((unsigned int) 0x00000004)
#define PINSEL0_P01_PWM3      ((unsigned int) 0x00000008)
#define PINSEL0_P01_EINT0     ((unsigned int) 0x0000000c)
#define PINSEL0_P01_MASK      ((unsigned int) 0x0000000c)

#define PINSEL0_P02_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P02_SCL0      ((unsigned int) 0x00000010)
#define PINSEL0_P02_CAP00     ((unsigned int) 0x00000020)
#define PINSEL0_P02_RSVD3     ((unsigned int) 0x00000030)
#define PINSEL0_P02_MASK      ((unsigned int) 0x00000030)

#define PINSEL0_P03_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P03_SDA0      ((unsigned int) 0x00000040)
#define PINSEL0_P03_MAT00     ((unsigned int) 0x00000080)
#define PINSEL0_P03_EINT1     ((unsigned int) 0x000000c0)
#define PINSEL0_P03_MASK      ((unsigned int) 0x000000c0)

#define PINSEL0_P04_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P04_SCK0      ((unsigned int) 0x00000100)
#define PINSEL0_P04_CAP01     ((unsigned int) 0x00000200)
#define PINSEL0_P04_AD06     ((unsigned int) 0x00000300)
#define PINSEL0_P04_MASK      ((unsigned int) 0x00000300)

#define PINSEL0_P05_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P05_MISO0     ((unsigned int) 0x00000400)
#define PINSEL0_P05_MAT01     ((unsigned int) 0x00000800)
#define PINSEL0_P05_AD07      ((unsigned int) 0x00000c00)
#define PINSEL0_P05_MASK      ((unsigned int) 0x00000c00)

#define PINSEL0_P06_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P06_MOSI0     ((unsigned int) 0x00001000)
#define PINSEL0_P06_CAP02     ((unsigned int) 0x00002000)
#define PINSEL0_P06_AD10      ((unsigned int) 0x00003000)
#define PINSEL0_P06_MASK      ((unsigned int) 0x00003000)

#define PINSEL0_P07_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P07_SSEL0     ((unsigned int) 0x00004000)
#define PINSEL0_P07_PWM2      ((unsigned int) 0x00008000)
#define PINSEL0_P07_EINT2     ((unsigned int) 0x0000c000)
#define PINSEL0_P07_MASK      ((unsigned int) 0x0000c000)

#define PINSEL0_P08_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P08_TXD1      ((unsigned int) 0x00010000)
#define PINSEL0_P08_PWM4      ((unsigned int) 0x00020000)
#define PINSEL0_P08_AD11      ((unsigned int) 0x00030000)
#define PINSEL0_P08_MASK      ((unsigned int) 0x00030000)

#define PINSEL0_P09_GPIO      ((unsigned int) 0x00000000)
#define PINSEL0_P09_RXD1      ((unsigned int) 0x00040000)
#define PINSEL0_P09_PWM6      ((unsigned int) 0x00080000)
#define PINSEL0_P09_EINT3     ((unsigned int) 0x000c0000)
#define PINSEL0_P09_MASK      ((unsigned int) 0x000c0000)

#define PINSEL0_P010_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P010_RTS1     ((unsigned int) 0x00100000)
#define PINSEL0_P010_CAP10    ((unsigned int) 0x00200000)
#define PINSEL0_P010_AD12     ((unsigned int) 0x00300000)
#define PINSEL0_P010_MASK     ((unsigned int) 0x00300000)

#define PINSEL0_P011_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P011_CTS1     ((unsigned int) 0x00400000)
#define PINSEL0_P011_CAP11    ((unsigned int) 0x00800000)
#define PINSEL0_P011_SCL1     ((unsigned int) 0x00c00000)
#define PINSEL0_P011_MASK     ((unsigned int) 0x00c00000)

#define PINSEL0_P012_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P012_DSR1     ((unsigned int) 0x01000000)
#define PINSEL0_P012_MAT10    ((unsigned int) 0x02000000)
#define PINSEL0_P012_AD13     ((unsigned int) 0x03000000)
#define PINSEL0_P012_MASK     ((unsigned int) 0x03000000)

#define PINSEL0_P013_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P013_DTR1     ((unsigned int) 0x04000000)
#define PINSEL0_P013_MAT11    ((unsigned int) 0x08000000)
#define PINSEL0_P013_AD14     ((unsigned int) 0x0c000000)
#define PINSEL0_P013_MASK     ((unsigned int) 0x0c000000)

#define PINSEL0_P014_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P014_DCD1     ((unsigned int) 0x10000000)
#define PINSEL0_P014_EINT1    ((unsigned int) 0x20000000)
#define PINSEL0_P014_SDA1     ((unsigned int) 0x30000000)
#define PINSEL0_P014_MASK     ((unsigned int) 0x30000000)

#define PINSEL0_P015_GPIO     ((unsigned int) 0x00000000)
#define PINSEL0_P015_RI1      ((unsigned int) 0x40000000)
#define PINSEL0_P015_EINT2    ((unsigned int) 0x80000000)
#define PINSEL0_P015_AD15     ((unsigned int) 0xc0000000)
#define PINSEL0_P015_MASK     ((unsigned int) 0xc0000000)

#define PINSEL1_P016_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P016_EINT0    ((unsigned int) 0x00000001)
#define PINSEL1_P016_MAT02    ((unsigned int) 0x00000002)
#define PINSEL1_P016_CAP02    ((unsigned int) 0x00000003)
#define PINSEL1_P016_MASK     ((unsigned int) 0x00000003)

#define PINSEL1_P017_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P017_CAP12    ((unsigned int) 0x00000004)
#define PINSEL1_P017_SCK1     ((unsigned int) 0x00000008)
#define PINSEL1_P017_MAT12    ((unsigned int) 0x0000000c)
#define PINSEL1_P017_MASK     ((unsigned int) 0x0000000c)

#define PINSEL1_P018_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P018_CAP13    ((unsigned int) 0x00000010)
#define PINSEL1_P018_MISO1    ((unsigned int) 0x00000020)
#define PINSEL1_P018_MAT13    ((unsigned int) 0x00000030)
#define PINSEL1_P018_MASK     ((unsigned int) 0x00000030)

#define PINSEL1_P019_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P019_MAT12    ((unsigned int) 0x00000040)
#define PINSEL1_P019_MOSI1    ((unsigned int) 0x00000080)
#define PINSEL1_P019_CAP12    ((unsigned int) 0x000000c0)
#define PINSEL1_P019_MASK     ((unsigned int) 0x000000c0)

#define PINSEL1_P020_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P020_MAT13    ((unsigned int) 0x00000100)
#define PINSEL1_P020_SSEL1    ((unsigned int) 0x00000200)
#define PINSEL1_P020_EINT3    ((unsigned int) 0x00000300)
#define PINSEL1_P020_MASK     ((unsigned int) 0x00000300)

#define PINSEL1_P021_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P021_PWM5     ((unsigned int) 0x00000400)
#define PINSEL1_P021_AD16     ((unsigned int) 0x00000800)
#define PINSEL1_P021_CAP13    ((unsigned int) 0x00000c00)
#define PINSEL1_P021_MASK     ((unsigned int) 0x00000c00)

#define PINSEL1_P022_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P022_AD17     ((unsigned int) 0x00001000)
#define PINSEL1_P022_CAP00    ((unsigned int) 0x00002000)
#define PINSEL1_P022_MAT00    ((unsigned int) 0x00003000)
#define PINSEL1_P022_MASK     ((unsigned int) 0x00003000)

#define PINSEL1_P023_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P023_VBUS     ((unsigned int) 0x00004000)
#define PINSEL1_P023_RSVD2    ((unsigned int) 0x00008000)
#define PINSEL1_P023_RSVD3    ((unsigned int) 0x0000c000)
#define PINSEL1_P023_MASK     ((unsigned int) 0x0000c000)

#define PINSEL1_P024_RSVD0    ((unsigned int) 0x00000000)
#define PINSEL1_P024_RSVD1    ((unsigned int) 0x00010000)
#define PINSEL1_P024_RSVD2    ((unsigned int) 0x00020000)
#define PINSEL1_P024_RSVD3    ((unsigned int) 0x00030000)
#define PINSEL1_P024_MASK     ((unsigned int) 0x00030000)

#define PINSEL1_P025_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P025_AD04     ((unsigned int) 0x00040000)
#define PINSEL1_P025_AOUT     ((unsigned int) 0x00080000)
#define PINSEL1_P025_RSVD3    ((unsigned int) 0x000c0000)
#define PINSEL1_P025_MASK     ((unsigned int) 0x000c0000)

#define PINSEL1_P026_RSVD0    ((unsigned int) 0x00000000)
#define PINSEL1_P026_RSVD1    ((unsigned int) 0x00100000)
#define PINSEL1_P026_RSVD2    ((unsigned int) 0x00200000)
#define PINSEL1_P026_RSVD3    ((unsigned int) 0x00300000)
#define PINSEL1_P026_MASK     ((unsigned int) 0x00300000)

#define PINSEL1_P027_RSVD0    ((unsigned int) 0x00000000)
#define PINSEL1_P027_RSVD1    ((unsigned int) 0x00400000)
#define PINSEL1_P027_RSVD2    ((unsigned int) 0x00800000)
#define PINSEL1_P027_RSVD3    ((unsigned int) 0x00c00000)
#define PINSEL1_P027_MASK     ((unsigned int) 0x00c00000)

#define PINSEL1_P028_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P028_AD01     ((unsigned int) 0x01000000)
#define PINSEL1_P028_CAP02    ((unsigned int) 0x02000000)
#define PINSEL1_P028_MAT02    ((unsigned int) 0x03000000)
#define PINSEL1_P028_MASK     ((unsigned int) 0x03000000)

#define PINSEL1_P029_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P029_AD02     ((unsigned int) 0x04000000)
#define PINSEL1_P029_CAP03    ((unsigned int) 0x08000000)
#define PINSEL1_P029_MAT03    ((unsigned int) 0x0c000000)
#define PINSEL1_P029_MASK     ((unsigned int) 0x0c000000)

#define PINSEL1_P030_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P030_AD03     ((unsigned int) 0x10000000)
#define PINSEL1_P030_EINT3    ((unsigned int) 0x20000000)
#define PINSEL1_P030_CAP00    ((unsigned int) 0x30000000)
#define PINSEL1_P030_MASK     ((unsigned int) 0x30000000)

#define PINSEL1_P031_GPIO     ((unsigned int) 0x00000000)
#define PINSEL1_P031_UPLED    ((unsigned int) 0x40000000)
#define PINSEL1_P031_CONNECT  ((unsigned int) 0x80000000)
#define PINSEL1_P031_RSVD3    ((unsigned int) 0xc0000000)
#define PINSEL1_P031_MASK     ((unsigned int) 0xc0000000)


#define GPIO_IO_P0      ((unsigned int) 0x00000001)
#define GPIO_IO_P1      ((unsigned int) 0x00000002)
#define GPIO_IO_P2      ((unsigned int) 0x00000004)
#define GPIO_IO_P3      ((unsigned int) 0x00000008)
#define GPIO_IO_P4      ((unsigned int) 0x00000010)
#define GPIO_IO_P5      ((unsigned int) 0x00000020)
#define GPIO_IO_P6      ((unsigned int) 0x00000040)
#define GPIO_IO_P7      ((unsigned int) 0x00000080)
#define GPIO_IO_P8      ((unsigned int) 0x00000100)
#define GPIO_IO_P9      ((unsigned int) 0x00000200)
#define GPIO_IO_P10     ((unsigned int) 0x00000400)
#define GPIO_IO_P11     ((unsigned int) 0x00000800)
#define GPIO_IO_P12     ((unsigned int) 0x00001000)
#define GPIO_IO_P13     ((unsigned int) 0x00002000)
#define GPIO_IO_P14     ((unsigned int) 0x00004000)
#define GPIO_IO_P15     ((unsigned int) 0x00008000)
#define GPIO_IO_P16     ((unsigned int) 0x00010000)
#define GPIO_IO_P17     ((unsigned int) 0x00020000)
#define GPIO_IO_P18     ((unsigned int) 0x00040000)
#define GPIO_IO_P19     ((unsigned int) 0x00080000)
#define GPIO_IO_P20     ((unsigned int) 0x00100000)
#define GPIO_IO_P21     ((unsigned int) 0x00200000)
#define GPIO_IO_P22     ((unsigned int) 0x00400000)
#define GPIO_IO_P23     ((unsigned int) 0x00800000)
#define GPIO_IO_P24     ((unsigned int) 0x01000000)
#define GPIO_IO_P25     ((unsigned int) 0x02000000)
#define GPIO_IO_P26     ((unsigned int) 0x04000000)
#define GPIO_IO_P27     ((unsigned int) 0x08000000)
#define GPIO_IO_P28     ((unsigned int) 0x10000000)
#define GPIO_IO_P29     ((unsigned int) 0x20000000)
#define GPIO_IO_P30     ((unsigned int) 0x40000000)
#define GPIO_IO_P31     ((unsigned int) 0x80000000)


///////////////////////////////////////////////////////////////////////////////
// A/D Converter
#define ADC             ((adcRegs_t *)0xE0034000)

// A/D Converter Registers
#define ADCR            ADC->cr         /* Control Register */
#define ADDR            ADC->dr         /* Data Register */


///////////////////////////////////////////////////////////////////////////////
// D/A Converter

#define DAC             ((dacRegs_t *)0xE006C000)

// D/A Converter Registers
#define DACR            DAC->dr        /* Data Register */
///////////////////////////////////////////////////////////////////////////////
// System Contol Block
#define SCB             ((scbRegs_t *)0xE01FC000)

// Memory Accelerator Module Registers (MAM)
#define MAMCR           SCB->mam.cr     /* Control Register */
#define MAMTIM          SCB->mam.tim    /* Timing Control Register */

// Memory Mapping Control Register
#define MEMMAP          SCB->memmap

// Phase Locked Loop Registers (PLL)
#define PLLCON          SCB->pll.con    /* Control Register */
#define PLLCFG          SCB->pll.cfg    /* Configuration Register */
#define PLLSTAT         SCB->pll.stat   /* Status Register */
#define PLLFEED         SCB->pll.feed   /* Feed Register */

/*
#define PLLCON_PLLE     (0x00000001)
#define PLLCON_PLLC     (0x00000002)
#define PLLCON_MASK     (0x00000003)

#define PLLCFG_MSEL     (0x0000001f)
#define PLLCFG_PSEL     (0x00000060)
#define PLLCFG_MUL1     (0x00000000)
#define PLLCFG_MUL2     (0x00000001)
#define PLLCFG_MUL3     (0x00000002)
#define PLLCFG_MUL4     (0x00000003)
#define PLLCFG_MUL5     (0x00000004)
#define PLLCFG_MUL6     (0x00000005)
#define PLLCFG_MUL7     (0x00000006)
#define PLLCFG_MUL8     (0x00000007)
#define PLLCFG_MUL9     (0x00000008)
#define PLLCFG_MUL10    (0x00000009)
#define PLLCFG_MUL11    (0x0000000a)
#define PLLCFG_MUL12    (0x0000000b)
#define PLLCFG_MUL13    (0x0000000c)
#define PLLCFG_MUL14    (0x0000000d)
#define PLLCFG_MUL15    (0x0000000e)
#define PLLCFG_MUL16    (0x0000000f)
#define PLLCFG_MUL17    (0x00000010)
#define PLLCFG_MUL18    (0x00000011)
#define PLLCFG_MUL19    (0x00000012)
#define PLLCFG_MUL20    (0x00000013)
#define PLLCFG_MUL21    (0x00000014)
#define PLLCFG_MUL22    (0x00000015)
#define PLLCFG_MUL23    (0x00000016)
#define PLLCFG_MUL24    (0x00000017)
#define PLLCFG_MUL25    (0x00000018)
#define PLLCFG_MUL26    (0x00000019)
#define PLLCFG_MUL27    (0x0000001a)
#define PLLCFG_MUL28    (0x0000001b)
#define PLLCFG_MUL29    (0x0000001c)
#define PLLCFG_MUL30    (0x0000001d)
#define PLLCFG_MUL31    (0x0000001e)
#define PLLCFG_MUL32    (0x0000001f)
#define PLLCFG_DIV1     (0x00000000)
#define PLLCFG_DIV2     (0x00000020)
#define PLLCFG_DIV4     (0x00000040)
#define PLLCFG_DIV8     (0x00000060)
#define PLLCFG_MASK     (0x0000007f)

#define PLLSTAT_MSEL    (0x0000001f)
#define PLLSTAT_PSEL    (0x00000060)
#define PLLSTAT_PLLE    (0x00000100)
#define PLLSTAT_PLLC    (0x00000200)
#define PLLSTAT_PLOCK   (0x00000400)

#define PLLFEED_FEED1   (0x000000aa)
#define PLLFEED_FEED2   (0x00000055)
*/

// Power Control Registers
#define PCON            SCB->p.con      /* Control Register */
#define PCONP           SCB->p.conp     /* Peripherals Register */

#define PCON_IDL        (0x00000001)
#define PCON_PD         (0x00000002)
#define PCON_PDBOD      (0x00000004)
#define PCON_BODPDM     (0x00000008)
#define PCON_BOGD       (0x00000010)
#define PCON_BORD       (0x00000020)
#define PCON_MASK       (0x0000003f)

#define PCONP_PCTIM0    (0x00000002)
#define PCONP_PCTIM1    (0x00000004)
#define PCONP_PCUART0   (0x00000008)
#define PCONP_PCUART1   (0x00000010)
#define PCONP_PCPWM0    (0x00000020)
#define PCONP_PCI2C0    (0x00000080)
#define PCONP_PCSPI0    (0x00000100)
#define PCONP_PCRTC     (0x00000200)
#define PCONP_PCSPI1    (0x00000400)
#define PCONP_PCAD0     (0x00001000)
#define PCONP_PCI2C1    (0x00080000)
#define PCONP_PCAD1     (0x00100000)
#define PCONP_PUSB      (0x80000000)
#define PCONP_MASK      (0x801817be)


// VPB Divider Register
#define VPBDIV          SCB->vpbdiv

// External Interrupt Registers
//#define EXTINT          SCB->ext.flag   /* Flag Register */
//#define EXTWAKE         SCB->ext.wake   /* Wakeup Register */
//#define EXTMODE         SCB->ext.mode   /* Mode Register */
//#define EXTPOLAR        SCB->ext.polar  /* Polarity Register */

//#define PCON		 *(volatile unsigned int *)0xE01FC0C0
//#define PCONP		 *(volatile unsigned int *)0xE01FC0C4

#define EXTINT   *(volatile unsigned int *)0xE01FC140
#define INTWAKE  *(volatile unsigned int *)0xE01FC144
#define EXTMODE  *(volatile unsigned int *)0xE01FC148
#define EXTPOLAR *(volatile unsigned int *)0xE01FC14C

#define EXTINT_EINT0    (0x00000001)
#define EXTINT_EINT1    (0x00000002)
#define EXTINT_EINT2    (0x00000004)
#define EXTINT_EINT3    (0x00000008)
#define EXTINT_MASK     (0x0000000f)

#define INTWAKE_EINT0   (0x00000001)
#define INTWAKE_EINT1   (0x00000002)
#define INTWAKE_EINT2   (0x00000004)
#define INTWAKE_EINT3   (0x00000008)
#define INTWAKE_USB     (0x00000020)
#define INTWAKE_BOD     (0x00004000)
#define INTWAKE_RTC     (0x00008000)
#define INTWAKE_MASK    (0x0000c02f)

#define EXTMODE_EINT0_EDGE  (0x00000001)
#define EXTMODE_EINT1_EDGE  (0x00000002)
#define EXTMODE_EINT2_EDGE  (0x00000004)
#define EXTMODE_EINT3_EDGE  (0x00000008)
#define EXTMODE_MASK			  (0x0000000f)

#define EXTPOLAR_EINT0_HI  	(0x00000001)
#define EXTPOLAR_EINT1_HI 	(0x00000002)
#define EXTPOLAR_EINT2_HI		(0x00000004)
#define EXTPOLAR_EINT3_HI 	(0x00000008)
#define EXTPOLAR_MASK   		(0x0000000f)


///////////////////////////////////////////////////////////////////////////////
// Vectored Interrupt Controller
#define VIC             ((vicRegs_t *)0xFFFFF000)

// Vectored Interrupt Controller Registers
#define VICIRQStatus    VIC->irqStatus  /* IRQ Status Register */
#define VICFIQStatus    VIC->fiqStatus  /* FIQ Status Register */
#define VICRawIntr      VIC->rawIntr    /* Raw Interrupt Status Register */
#define VICIntSelect    VIC->intSelect  /* Interrupt Select Register */
#define VICIntEnable    VIC->intEnable  /* Interrupt Enable Register */
#define VICIntEnClear   VIC->intEnClear /* Interrupt Enable Clear Register */
#define VICSoftInt      VIC->softInt    /* Software Interrupt Register */
#define VICSoftIntClear VIC->softIntClear /* Software Interrupt Clear Register */
#define VICProtection   VIC->protection /* Protection Enable Register */
#define VICVectAddr     VIC->vectAddr   /* Vector Address Register */
#define VICDefVectAddr  VIC->defVectAddr /* Default Vector Address Register */
#define VICVectAddr0    VIC->vectAddr0  /* Vector Address 0 Register */
#define VICVectAddr1    VIC->vectAddr1  /* Vector Address 1 Register */
#define VICVectAddr2    VIC->vectAddr2  /* Vector Address 2 Register */
#define VICVectAddr3    VIC->vectAddr3  /* Vector Address 3 Register */
#define VICVectAddr4    VIC->vectAddr4  /* Vector Address 4 Register */
#define VICVectAddr5    VIC->vectAddr5  /* Vector Address 5 Register */
#define VICVectAddr6    VIC->vectAddr6  /* Vector Address 6 Register */
#define VICVectAddr7    VIC->vectAddr7  /* Vector Address 7 Register */
#define VICVectAddr8    VIC->vectAddr8  /* Vector Address 8 Register */
#define VICVectAddr9    VIC->vectAddr9  /* Vector Address 9 Register */
#define VICVectAddr10   VIC->vectAddr10 /* Vector Address 10 Register */
#define VICVectAddr11   VIC->vectAddr11 /* Vector Address 11 Register */
#define VICVectAddr12   VIC->vectAddr12 /* Vector Address 12 Register */
#define VICVectAddr13   VIC->vectAddr13 /* Vector Address 13 Register */
#define VICVectAddr14   VIC->vectAddr14 /* Vector Address 14 Register */
#define VICVectAddr15   VIC->vectAddr15 /* Vector Address 15 Register */
#define VICVectCntl0    VIC->vectCntl0  /* Vector Control 0 Register */
#define VICVectCntl1    VIC->vectCntl1  /* Vector Control 1 Register */
#define VICVectCntl2    VIC->vectCntl2  /* Vector Control 2 Register */
#define VICVectCntl3    VIC->vectCntl3  /* Vector Control 3 Register */
#define VICVectCntl4    VIC->vectCntl4  /* Vector Control 4 Register */
#define VICVectCntl5    VIC->vectCntl5  /* Vector Control 5 Register */
#define VICVectCntl6    VIC->vectCntl6  /* Vector Control 6 Register */
#define VICVectCntl7    VIC->vectCntl7  /* Vector Control 7 Register */
#define VICVectCntl8    VIC->vectCntl8  /* Vector Control 8 Register */
#define VICVectCntl9    VIC->vectCntl9  /* Vector Control 9 Register */
#define VICVectCntl10   VIC->vectCntl10 /* Vector Control 10 Register */
#define VICVectCntl11   VIC->vectCntl11 /* Vector Control 11 Register */
#define VICVectCntl12   VIC->vectCntl12 /* Vector Control 12 Register */
#define VICVectCntl13   VIC->vectCntl13 /* Vector Control 13 Register */
#define VICVectCntl14   VIC->vectCntl14 /* Vector Control 14 Register */
#define VICVectCntl15   VIC->vectCntl15 /* Vector Control 15 Register */



#endif
