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

/* skinit.c code to prepare the environment for skinit
 * Written for TrustVisor by Ning Qu
 */

#include <types.h>
#include <error.h>
#include <multiboot.h>
#include <string.h>
#include <relocate.h>
#include <print.h>
#include <svm.h>
#include <visor.h>
#include <paging.h>
#include <msr.h>
#include <processor.h>
#include <e820.h>
#include <loader.h>
#include <delay.h>
#include <tpm.h>
#include <ucode.h>

enum tis_init tis_init(void);
int tis_access(int locality);
int TPM_Startup_Clear(void);
int tis_deactivate_all(void);

int prepare_tpm(void)
{
  int tpm, res;

  if ((tpm = tis_init()) <= 0) {
    return -1;
  }

  if (!tis_access(TIS_LOCALITY_0)) {
    EARLY_FAIL();
  }

  if ((res = TPM_Startup_Clear()) && (res != 0x26)) {
    EARLY_FAIL();
  }

  if (tis_deactivate_all()) {
    EARLY_FAIL();
  }
  return 0;
}


void enable_svm(void)
{
  u32 msrlo, msrhi;

  rdmsr(MSR_EFER, &msrlo, &msrhi);
  wrmsr(MSR_EFER, msrlo | EFER_SVME, msrhi);
}

void stop_aps(void)
{
  u32 msrlo, msrhi;
  u32 apic_base;

  /* Check if APIC enabled */
  rdmsr(LAPIC_BASE_MSR, &msrlo, &msrhi);

  if (!(msrlo & LAPIC_BASE_MSR_ENABLE) ||
      !(msrlo & LAPIC_BASE_MSR_BSP)) {
    /* Something wrong with APIC initialization */
    EARLY_FAIL();
  }

  apic_base = msrlo & 0xfffff000;
  
  /* Level Trigger need to add LAPIC_INT_LEVELTRIG | LAPIC_INT_ASSERT */
  lapic_write(apic_base, LAPIC_ICR, LAPIC_DM_INIT | LAPIC_DEST_ALLBUT | LAPIC_ICR_ASSERT);

  while (lapic_read(apic_base, LAPIC_ICR) & LAPIC_ICR_BUSY);
}

void prepare_skinit(void)
{
    int rv;
    
    if ((rv = prepare_tpm()) < 0) {
        putstr("ERROR: prepare_tpm returned error (watch out for endianness): ");
        putbytes((u8*)&rv, sizeof(int));
        putstr("Continuing anyways...\n");
    }

    enable_svm();    
    
    /* clear microcode on all the APs */
    if (!init_all_aps()) {
        putstr("init_all_aps() returned false!\n");
        return;// false;
    }
    
    if (!clear_microcode()) {
        putstr("clear_microcode() returned false!\n");
        return;// false;
    }
    putstr("BSP microcode cleared.\n");
    
    /* put all APs in INIT */
    if (!init_all_aps()) {
        putstr("init_all_aps()2 returned false!\n");
        return;// false;
    }
    
    putstr("Microcode clear SUCCEEDED; calculated PCR-17 should match actual.\n");
    //stop_aps(); // orig code from Michael / OSLO?
}


#define TIS_BASE_PHYS 0xfed40000

static int tis_locality;

/**
 * Init the TIS driver.
 * Returns a TIS_INIT_* value.
 */
enum tis_init tis_init(void)
{
    struct tis_id *id;
    int i;

    id = (struct tis_id *)(TIS_BASE_PHYS + TPM_DID_VID_0);
    i = id->did_vid;
    
    switch (id->did_vid)
    {
        case 0x2e4d5453:   /* "STM." */
            return TIS_INIT_STM;
        case 0xb15d1:
            return TIS_INIT_INFINEON;
        case 0x100214e4: /* Broadcom */
            return TIS_INIT_BROADCOM;
	case 0x4a100000: /* Dell T105 */
            return TIS_INIT_OTHERS;
	case 0x32031114: /* Dell Optiplex 740 */
            return TIS_INIT_OTHERS;
        case 0:
        case -1:
            return TIS_INIT_NO_TPM;
        default:
            return TIS_INIT_NO_TPM;
    }
}

int tis_access(int locality)
{
  volatile struct tis_mmap *mmap;

  tis_locality = TIS_BASE_PHYS + locality;
  mmap = (struct tis_mmap *) tis_locality;


  if(!(mmap->access & TIS_ACCESS_VALID)) {
      return 0;
  }
  if(mmap->access & TIS_ACCESS_ACTIVE) {
      return 1;
  }

  // first try it the normal way
  mmap->access = TIS_ACCESS_REQUEST;

  mdelay(10);

  // make the tpm ready -> abort a command
  mmap->sts_base = TIS_STS_CMD_READY;
  
  return mmap->access & TIS_ACCESS_ACTIVE;

}

unsigned long tis_ntohl(unsigned long in) {
    unsigned char *s = (unsigned char *)&in;
    return (unsigned long)(s[0] << 24 | s[1] << 16 | s[2] << 8 | s[3]);
}

void wait_state(volatile struct tis_mmap *mmap, unsigned state)
{
    unsigned i;
    
    for (i=0; i<750; i++) {
        if((mmap->sts_base & state)==state) {
            return;
        }
        mdelay(1);
    }
}

/**
 * Write the given buffer to the TPM.
 * Returns the numbers of bytes transfered or an value < 0 on errors.
 */
int tis_write(const unsigned char *buffer, unsigned int size)
{
  volatile struct tis_mmap *mmap = (struct tis_mmap *) tis_locality;
  int res;

  if (!(mmap->sts_base & TIS_STS_CMD_READY))
  {
      // make the tpm ready -> wakeup from idle state
      mmap->sts_base = TIS_STS_CMD_READY;
      wait_state(mmap, TIS_STS_CMD_READY);
      mmap->sts_base = TIS_STS_CMD_READY;                
  }
  if (!(mmap->sts_base & TIS_STS_CMD_READY))
    return -1;

  for(res=0; (unsigned int)res < size;res++)
      mmap->data_fifo = *buffer++;

  wait_state(mmap, TIS_STS_VALID);

  if(mmap->sts_base & TIS_STS_EXPECT) {
      return -2;
  } 

  // execute the command
  mmap->sts_base = TIS_STS_TPM_GO;    

  return res;
}


/**
 * Read into the given buffer from the TPM.
 * Returns the numbers of bytes received or an value < 0 on errors.
 */
int tis_read(unsigned char *buffer, unsigned int size)
{
  volatile struct tis_mmap *mmap = (struct tis_mmap *) tis_locality;
  int res = 0;

  wait_state(mmap, TIS_STS_VALID | TIS_STS_DATA_AVAIL);
  if(!(mmap->sts_base & TIS_STS_VALID)) {
      return -2;
  }

  for (res=0; (unsigned int)res < size && mmap->sts_base & TIS_STS_DATA_AVAIL; res++)
      *buffer++ = mmap->data_fifo;

  if(mmap->sts_base & TIS_STS_DATA_AVAIL) {
      return -3;
  }

  /* if we're reading 0 bytes, don't make the tpm 'ready' again */
  if(!res) { return res; } 
  
  // make the tpm ready again -> this allows tpm background jobs to complete
  mmap->sts_base = TIS_STS_CMD_READY;

  return res;
}


/**
 * Transmit a command to the TPM and wait for the response.
 * This is our high level TIS function used by all TPM commands.
 */
int tis_transmit(const unsigned char *write_buffer, unsigned write_count, unsigned char *read_buffer, unsigned read_count)
{
  unsigned int res;

  res = tis_write(write_buffer, write_count);
  if (res <= 0)
    return -1;
  
  res = tis_read(read_buffer, read_count);
  if (res <= 0)
    return -2;

  return res;
}

/**
 * Send a startup to the TPM.
 *
 * Note: We could use the TPM_TRANSMIT_FUNC macro, but this generates smaller code.
 */
int TPM_Startup_Clear(void)
{
  unsigned char buffer[TCG_BUFFER_SIZE];
  int res;

  ((u32 *)buffer)[0] = 0x0000c100;
  ((u32 *)buffer)[1] = 0x00000c00;
  ((u32 *)buffer)[2] = 0x01009900;

  res = tis_transmit(buffer, 12, buffer, TCG_BUFFER_SIZE);

  return res < 0 ? res : (int) tis_ntohl(*((u32 *) (buffer + 6)));
}

/**
 * Deactivate all localities.
 * Returns zero if no locality is active.
 */
int tis_deactivate_all(void)
{
  int res = 0;
  unsigned i;
  for (i=0; i<4; i++)
    {
      volatile struct tis_mmap *mmap = (struct tis_mmap *)(TIS_BASE_PHYS+(i<<12));
      if (mmap->access!= 0xff)
	{
	  mmap->access = TIS_ACCESS_ACTIVE;
	  res |= mmap->access & TIS_ACCESS_ACTIVE;
	}
    }
  return res;
}

