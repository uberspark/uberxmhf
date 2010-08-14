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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

#include <types.h>	
#include <multiboot.h>
#include <loader.h>
#include <msr.h>
#include <visor.h>
#include <ucode.h>

/*
 * Definitions for APIC
 */ 
#define MSR_IA32_APICBASE		0x1b
#define MSR_IA32_APICBASE_BSP		(1<<8)
#define MSR_IA32_APICBASE_ENABLE	(1<<11)
#define MSR_IA32_APICBASE_BASE		(0xfffff<<12)

/*
 * Definitions for atomic operations
 */

#define LOCK "lock ; "
typedef struct __packed { uint32_t counter; } atomic_t;

/* halt barrier for all the APs */
static atomic_t ap_halt_count;

/* microcode-successfully-cleared barrier for all the APs */
static atomic_t ap_ucode_clear_count;

/**
 * atomic_inc - increment atomic variable
 * @v: pointer of type atomic_t
 * 
 * Atomically increments @v by 1.  Note that the guaranteed
 * useful range of an atomic_t is only 24 bits.
 */ 
static __inline__ void atomic_inc(atomic_t *v)
{
        __asm__ __volatile__(
                LOCK "incl %0"
                :"=m" (*(volatile int *)&v->counter)
                :"m" (*(volatile int *)&v->counter));
}

/**
 * atomic_set - set atomic variable
 * @v: pointer of type atomic_t
 * @i: required value
 * 
 * Atomically sets the value of @v to @i.  Note that the guaranteed
 * useful range of an atomic_t is only 24 bits.
 */ 
#define _atomic_set(v,i)        (((v).counter) = (i))
#define atomic_set(v,i)         (*(volatile int *)&((v)->counter) = (i))

/**
 * atomic_read - read atomic variable
 * @v: pointer of type atomic_t
 * 
 * Atomically reads the value of @v.  Note that the guaranteed
 * useful range of an atomic_t is only 24 bits.
 */
#define _atomic_read(v)         ((v).counter)
#define atomic_read(v)          (*(volatile int *)&((v)->counter))


/*
 * Definitions for IO ports
 */
static inline unsigned int in(unsigned short port)
{
    unsigned int _v;

    __asm__ __volatile__ ("in %w1, %0"
                          : "=a" (_v) : "Nd" (port));

    return _v;
}

static inline void out(unsigned int value, unsigned short port)
{
    __asm__ __volatile__ ("out %0, %w1"
                          : : "a" (value), "Nd" (port));
}

/*
 * Definitions for MSRs
 */
#define rdmsrl(msr,val) do { unsigned long a__,b__; \
       __asm__ __volatile__("rdmsr" \
                            : "=a" (a__), "=d" (b__) \
                            : "c" (msr)); \
       val = a__ | ((u64)b__<<32); \
} while(0);

static inline void cpu_relax(void)
{
    __asm__ __volatile__ ( "rep;nop" : : : "memory" );
}

inline void *loader_memcpy(void * to, const void * from, u32 n)
{
  int d0, d1, d2;

  __asm__ __volatile__(
        "rep ; movsl\n\t"
        "movl %4,%%ecx\n\t"
        "andl $3,%%ecx\n\t"
#if 1   /* want to pay 2 byte penalty for a chance to skip microcoded rep? */
        "jz 1f\n\t"
#endif
        "rep ; movsb\n\t"
        "1:"
        : "=&c" (d0), "=&D" (d1), "=&S" (d2)
        : "0" (n/4), "g" (n), "1" ((long) to), "2" ((long) from)
        : "memory");
  return (to);
}


/* host bridge addresses */
#define	HB_HT_CFG		PCI_BDF(0, 0x18, 0)	/* HT config */
#define	HB_MISC_CTL		PCI_BDF(0, 0x18, 3)	/* Misc control */

#define	PCI_ID_AMD_RS780	0x96001022		/* RS780 */

/* PCI config definitions */
#define	PCI_CFG_ADDR		0x0cf8			/* PCI config space */
#define	PCI_CFG_DATA		0x0cfc
#define PCI_BDF(b, d, f)	(((b) << 8) | ((d) << 3) | (f))

/* APIC definitions */
#define	APIC_ICR		0x300
#define         APIC_DEST_ALLBUT        0xC0000
#define		APIC_INT_EDGE		0x00000
#define         APIC_INT_ASSERT         0x04000
#define         APIC_ICR_BUSY           0x01000
#define         APIC_DM_INIT            0x00500
#define         APIC_DM_STARTUP         0x00600

#define AP_TIMEOUT		0x01000000

extern bool core_clear_microcode(void);
extern bool core_load_microcode(void);

/* AP trampoline */
extern char *svm_ap_trampoline;
extern uint32_t svm_ap_trampoline_size;

/* DEV bitmap */
extern uint8_t dev_bitmap[0x20000];

/* what to do when an AP wakes up */
wakeup_state_t ap_wakeup_state;


static inline uint32_t pci_cfg_readl(uint32_t bdf, uint8_t reg)
{
    out(0x80000000 | (bdf << 8) | (reg & ~3), PCI_CFG_ADDR);
    return in(PCI_CFG_DATA);
}

static inline void pci_cfg_writel(uint32_t bdf, uint8_t reg, uint32_t val)
{
    out(0x80000000 | (bdf << 8) | (reg & ~3), PCI_CFG_ADDR);
    out(val, PCI_CFG_DATA);
}

static bool send_ipi(uint32_t dm)
{
    uint32_t timeout = AP_TIMEOUT;
    uint32_t *apic_icr_low;
    unsigned long long apicbase;

    rdmsrl(MSR_IA32_APICBASE, apicbase);

    apic_icr_low = (uint32_t *) ((uint32_t)(apicbase & ~0xFFF) + APIC_ICR);
    *apic_icr_low = APIC_DEST_ALLBUT | APIC_INT_EDGE | APIC_INT_ASSERT | dm;

    while (--timeout > 0 && (*apic_icr_low & APIC_ICR_BUSY))
        cpu_relax();

    if (timeout == 0) {
        putstr("send ipi timed-out\n");
        return false;
    }

    return true;
}

bool init_all_aps(void)
{
    return send_ipi(APIC_DM_INIT);
}

#define TBOOT_S3_WAKEUP_ADDR 0x8a000 /* somewhat hack-tastic -Jon */
bool start_all_aps(void)
{
    int naps = ((pci_cfg_readl(HB_HT_CFG, 0x60) >> 16) & 0x3F);
    int i;

    loader_memcpy((char *) TBOOT_S3_WAKEUP_ADDR,
    	&svm_ap_trampoline, svm_ap_trampoline_size);

    atomic_set(&ap_halt_count, 0);
    atomic_set(&ap_ucode_clear_count, 0);

    if (!send_ipi(APIC_DM_STARTUP | TBOOT_S3_WAKEUP_ADDR >> 12))
    	return false;

    //printk("Start all %d APs\n", naps);
    putstr("Start all APs to clear their microcode.\n");
    for(i=0; i<naps; i++)
        /* Just print the same message over and over, since
         * that's all we can do at the moment */
        putstr("There's an AP corresponding to this line.\n");
    
    while (atomic_read(&ap_halt_count) != naps) {
        putstr("looping on ap_halt_count\n");
    	/* wait until all APs halted */;
    }
    putstr("ap_halt_count now = naps\n");

    for(i=0; i<atomic_read(&ap_ucode_clear_count); i++)
        /* Just print the same message over and over, since
         * that's all we can do at the moment */
        putstr("There's an AP with cleared microcode corresponding to this line.\n");
    
    return true;
}

bool core_clear_microcode(void)
{
    uint32_t id;

    asm volatile("rdmsr" : "=a" (id) : "c" (0x0000008B)); /* get patch id */

    if (id != 0) {
        asm volatile("wrmsr" :: "c" (0xc0010021)); /* clear patch */
        //printk("CPU %d: Cleared microcode patch (was %08x)\n", get_apicid(), id);
        /* Can't print from here unless it's SMP-compatible */
        //putstr("CPU %d: Cleared microcode patch (was %08x)\n");
    }

    return true;
}

bool clear_microcode(void)
{
    /* clear all APs */
    ap_wakeup_state = CLEAR_MICROCODE;
    if (!start_all_aps()) {
        putstr("start_all_aps() returned false\n");
        return false;
    }

    putstr("start_all_aps() returned true :-)\n");
    
    /* clear the BSP */
    return core_clear_microcode();
}

void svm_ap_wakeup(void)
{
    switch (ap_wakeup_state) {
    case CLEAR_MICROCODE:
    	if(core_clear_microcode()) {
            atomic_inc(&ap_ucode_clear_count);
        }
	break;
    case LOAD_MICROCODE:
    	//(void) core_load_microcode();
	break;
    }

    /* halt this AP */
    atomic_inc(&ap_halt_count);
    for (;;)
    	asm volatile("hlt");
}


