/*
	broadcom 2837 (raspberry pi 3) definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __BCM2837_H__
#define __BCM2837_H__

#define BCM2837_PERIPHERAL_BASE		0x3f000000
#define BCM2837_MAXCPUS				4

//GPIO registers
#define GPFSEL1         (BCM2837_PERIPHERAL_BASE+0x00200004)
#define GPPUD           (BCM2837_PERIPHERAL_BASE+0x00200094)
#define GPPUDCLK0       (BCM2837_PERIPHERAL_BASE+0x00200098)

//Auxillary registers control
#define AUX_ENABLES     (BCM2837_PERIPHERAL_BASE+0x00215004)

//Auxillary registers -- Mini UART
#define AUX_MU_IO_REG   (BCM2837_PERIPHERAL_BASE+0x00215040)
#define AUX_MU_IER_REG  (BCM2837_PERIPHERAL_BASE+0x00215044)
#define AUX_MU_IIR_REG  (BCM2837_PERIPHERAL_BASE+0x00215048)
#define AUX_MU_LCR_REG  (BCM2837_PERIPHERAL_BASE+0x0021504C)
#define AUX_MU_MCR_REG  (BCM2837_PERIPHERAL_BASE+0x00215050)
#define AUX_MU_LSR_REG  (BCM2837_PERIPHERAL_BASE+0x00215054)
#define AUX_MU_MSR_REG  (BCM2837_PERIPHERAL_BASE+0x00215058)
#define AUX_MU_SCRATCH  (BCM2837_PERIPHERAL_BASE+0x0021505C)
#define AUX_MU_CNTL_REG (BCM2837_PERIPHERAL_BASE+0x00215060)
#define AUX_MU_STAT_REG (BCM2837_PERIPHERAL_BASE+0x00215064)
#define AUX_MU_BAUD_REG (BCM2837_PERIPHERAL_BASE+0x00215068)


#define ARMLOCALREGISTERS_BASE					0x40000000
#define ARMLOCALREGISTERS_MAILBOXWRITE_BASE		(ARMLOCALREGISTERS_BASE + 0x80)

#ifndef __ASSEMBLY__

typedef struct {
	u32 mailbox0write;
	u32 mailbox1write;
	u32 mailbox2write;
	u32 mailbox3write;
} armlocalregisters_mailboxwrite_t __attribute__((packed));

extern armlocalregisters_mailboxwrite_t *armlocalregisters_mailboxwrite[BCM2837_MAXCPUS];

#endif // __ASSEMBLY__

#endif //__BCM2837_H__
