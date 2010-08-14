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

/* intercepts-spt.c routines to handle all intercepts for shadow paging
 * argument for each handler is the struct of registers struct regs
 * defined in svm.h, and global vmcb_struct* linux_vmcb
 * 
 * Written for TrustVisor by Mark Luk and Ning Qu
 */

#include <types.h>
#include <processor.h>
#include <error.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <svm.h>
#include <print.h>
#include <string.h>
#include <sha1.h>
#include <prot.h>
#include <msr.h>
#include <io.h>
#include <pci.h>
#include <dev.h>
#include <scode.h>
#include <tpm.h>
#include <tpm_sw.h>

void handle_intercept(struct regs *greg);
void handle_vmmcall(struct regs *greg);
void handle_npf(void);
void handle_msr(struct regs *greg);
void handle_ioio(void);

/* decode read and write instructions, instruction format:
 * REX (1b, optional) OP (2b) MODRM (1b)
 * here, we don't deal with the case wit REX, so we conly 
 * care about MODRM field, the format of it
 *   7 6 | 5 4 3 | 2 1 0
 *   mod    CRn	   reg
 * And decoding reg is as following:
 *   eax	0
 *   ecx	1
 *   edx	2
 *   ebx	3
 *   esp        4
 *   ebp        5
 *   esi        6
 *   edi        7
 */
u32 REG_RD(u32 regnum, u32 *gregs){					
  u32 value;
  if (regnum == 0)			
    value = (u32)(linux_vmcb->rax);	
  else 				
  {					
    if (regnum == 4)			
      value = (u32)(linux_vmcb->rsp);	
    else				
      value = gregs[regnum];		
  }					
  return value;
}

void REG_WR(u32 value, u32 regnum, u32 *gregs)
{					
  if (regnum == 0)			
    (linux_vmcb->rax) = (u64)value;	
  else 				
  {					
    if (regnum == 4)			
      (linux_vmcb->rsp) = (u64)value;	
    else				
      gregs[regnum] = value;		
  }					
}

/* handler for all the intercepts, we dispatch it based on teh exitcode */
void handle_intercept(struct regs *greg) {
  /* detect if guest system disables cache before we intercept it,
   * if so, we need to synchronize the cache and physical memory 
   */
  VMCB_PRE_SYNC(linux_vmcb->cr0);
  /* cancel automatic TLB invalidation if set last time */
  VMCB_TLB_NOTHING();

  switch(linux_vmcb->exitcode) {
  case VMEXIT_MSR:
    handle_msr(greg);
    break;
  case VMEXIT_IOIO:
    handle_ioio();
    break;
  case VMEXIT_NPF:
    handle_npf();
    break;
  case VMEXIT_VMMCALL:
    DEBUG printf("INFO: intercepted vmmcall (exitcode %x, eip 0x%x)\n", (u32)linux_vmcb->exitcode, (u32)linux_vmcb->rip);
    handle_vmmcall(greg);
    break;
  default:
    printf("FATAL ERROR: Unexpected exceptions intercepted (exitcode 0x%x, eip 0x%x)\n", 
            (u32)linux_vmcb->exitcode, (u32)linux_vmcb->rip);
    FORCE_CRASH();
  }

  /* detect if guest system disables cache before we intercept it,
   * if so, we need to synchronize the cache and physical memory 
   */
  VMCB_POST_SYNC(linux_vmcb->cr0);
  linux_vmcb->tlb_control = TLB_CONTROL_FLUSHALL;
  return;
}

/* handler to process vmmcall intercept,
 * we use vmmcall to setup different things, so eax contains
 * the operation type information 
 */
void handle_vmmcall(struct regs *greg)
{
  u32 *gregs = (u32 *)greg;
  u32 cmd = (u32)linux_vmcb->rax;

  DEBUG printf("DEBUG: CPU CR3 value before vmmcall is %#lx\n", read_cr3());
  switch (cmd)
  {
  /* register the scode */
  case VISOR_SCMD_REG:
    {
      u32 scode_info, scode_sp, scode_pm, scode_en;
      /* sensitive code as guest virtual address in ebx */
      scode_info = REG_RD(3, gregs);
      /* sensitive code stack in edx */
      scode_sp = REG_RD(2, gregs);
      /* sensitive code params information addres in esi */
      scode_pm = REG_RD(6, gregs);
	  /* sensitive code entry point in edi */
	  scode_en = REG_RD(7, gregs);

      scode_register(linux_vmcb->cr3, scode_info, scode_sp, scode_pm, scode_en);

      linux_vmcb->rip += 3;
      break;
    }
  /* unregister the scode */
  case VISOR_SCMD_UNREG:
    {
      u32 scode_gva;
      /* sensitive code as guest virtual address in ebx */
      /* buffer address as guest virtual address in ebx */
      scode_gva = REG_RD(3, gregs);

      scode_unregister(linux_vmcb->cr3, scode_gva);

      linux_vmcb->rip += 3;
      break;
    }
  /* software TPM: readpcr */
  case VISOR_STPM_PCRREAD:
    {
      u32 buf_addr, num;
      /* buffer address in ebx */
      buf_addr = REG_RD(3, gregs);
      /* pcr number */
      num = REG_RD(1, gregs);
      DEBUG printf("DEBUG: PCR %d READ\n", num);
      scode_pcrread(linux_vmcb->cr3, buf_addr, num);
      
      linux_vmcb->rip += 3;
      break;
    }
  /* software TPM: extend */
  case VISOR_STPM_EXTEND:
    {
      u32 addr, len, num;
      /* buffer address in ebx */
      addr = REG_RD(3, gregs);
      /* data len  in ecx */
      len = REG_RD(1, gregs);
      /* pcr number */
      num = REG_RD(2, gregs);
      DEBUG printf("DEBUG: extend PCR %d, addr %#x, len %#x\n", num, addr, len);
      scode_pcrextend(linux_vmcb->cr3, addr, len, num);
      DEBUG printf("DEBUG: scode extend finish\n");
      linux_vmcb->rip += 3;
	  break;
    }

  case VISOR_STPM_SEAL:
    {
	  u32 data_addr, data_len, pcr_addr, out_addr, out_len_addr;
	  /* address of data to be sealed in eax*/
	  data_addr = REG_RD(3, gregs);
      /* data len in ebx */
	  data_len = REG_RD(1, gregs);
      /* pcr hash at release in ecx */
	  pcr_addr = REG_RD(2, gregs);
	  /* output address in esi */
      out_addr = REG_RD(6, gregs);
	  /* address to save output data length in edi */
	  out_len_addr = REG_RD(7, gregs);
	  
	  scode_seal(linux_vmcb->cr3, data_addr, data_len, pcr_addr, out_addr, out_len_addr);
      
	  linux_vmcb->rip += 3;

	  break;
	}

  case VISOR_STPM_UNSEAL:
    {
	  u32 input_addr, in_len, out_addr, out_len_addr;
	  /* address of data to be sealed in eax*/
	  input_addr = REG_RD(7, gregs);
	  /* data len in ebx */
	  in_len = REG_RD(1, gregs);
	  /* output address in ecx */
	  out_addr = REG_RD(2, gregs);
	  /* address to save output data length in esi */
	  out_len_addr = REG_RD(6, gregs);

      scode_unseal(linux_vmcb->cr3, input_addr, in_len, out_addr, out_len_addr);
      //DEBUG printf("scode unseal return\n");
      linux_vmcb->rip += 3;
	  break;
	}
  case VISOR_STPM_QUOTE:
   {
     u32 nonce_addr, out_addr, out_len_addr;
	 /* address of external nonce */
     nonce_addr = REG_RD(3, gregs);
	 /* address to save quote result */
	 out_addr = REG_RD(1, gregs);
	 /* address to save quote length */
	 out_len_addr = REG_RD(2, gregs);

	 scode_quote(linux_vmcb->cr3, nonce_addr,  out_addr, out_len_addr);
	 linux_vmcb->rip += 3;
	 break;
   }

  case VISOR_STPM_RAND:
   {
     u32 buffer_addr, numbytes_requested, numbytes_addr;
     /* address to save the random data*/
     buffer_addr = REG_RD(3, gregs);
     /* the number of bytes requested*/
     numbytes_requested = REG_RD(1, gregs);
     /* address to save the number of bytes generated*/
     numbytes_addr = REG_RD(2, gregs);
     DEBUG printf("DEBUG: vmcall stmp rand\n");
     scode_rand(linux_vmcb->cr3, buffer_addr, numbytes_requested, numbytes_addr);
     linux_vmcb->rip += 3;

     break;
   }
   /*
  case VISOR_STPM_GETPUBKEY:
    {
      u32 output;
      output = REG_RD(3, gregs);
      DEBUG printf("DEBUG: Get Pub Key! Buf addr %#x\n", output);
      scode_getpubkey(linux_vmcb->cr3, output);
      linux_vmcb->rip += 3;
      break;
    }
   */
/**
 * The purpose of these LTSTATE functions is to allow cooperation
 * with the untrusted OS so that the ciphertext of TrustVisor's
 * long-term secret state can be stored by the untrusted OS.
 * Right now that state is still not fully defined, so we just use
 * 512 bytes of meaningless data for testing.
 */
#define TMP_SIZE 512
  case VISOR_LTSTATE_GETSIZE:
    {
      u32 g_size_ptr;
      printf("VISOR_LTSTATE_GETSIZE ");
      /* size ptr in ebx */
      g_size_ptr = REG_RD(3, gregs);
      printf("g_size_ptr %08x\n", g_size_ptr);

      put_32bit_aligned_value_to_guest((u64)linux_vmcb->cr3, g_size_ptr, TMP_SIZE);
                
      /* Return to the _next_ instruction */
      linux_vmcb->rip += 3;
      break;
    }
  case VISOR_LTSTATE_GET:
    {
      u8 buf[TMP_SIZE];
      u32 g_size_ptr, g_buf_ptr, i;
      u32 g_size;
      printf("VISOR_LTSTATE_GET ");
      /* size ptr in ebx */
      g_size_ptr = REG_RD(3, gregs);
      /* buf ptr in ecx */
      g_buf_ptr = REG_RD(1, gregs);
      printf("g_size_ptr %08x g_buf_ptr %08x\n", g_size_ptr, g_buf_ptr);

      g_size = get_32bit_aligned_value_from_guest((u64)linux_vmcb->cr3, g_size_ptr);      
      printf("size from guest %d\n", g_size);

      /* Create some data to send back */
      for(i=0; i<TMP_SIZE; i++) {
          ((unsigned char *)buf)[i] = i;
      }
      g_size = TMP_SIZE;

      copy_to_guest((u64)linux_vmcb->cr3, g_buf_ptr, buf, g_size);
      put_32bit_aligned_value_to_guest((u64)linux_vmcb->cr3, g_size_ptr, g_size);
                
      /* Return to the _next_ instruction */
      linux_vmcb->rip += 3;
      break;
    }
  case VISOR_LTSTATE_PUT:
    {
      u32 g_size; /* guest passes actual size; not pointer to size as in get */
      u32 g_buf_ptr;
      u8 buf[TMP_SIZE];
      printf("VISOR_LTSTATE_PUT ");
      /* actual size in ebx */
      g_size = REG_RD(3, gregs);
      printf("g_size %d\n", g_size);
      /* buf ptr in ecx */
      g_buf_ptr = REG_RD(1, gregs);
      printf("g_buf_ptr %08x\n", g_buf_ptr);

      copy_from_guest(buf, (u64)linux_vmcb->cr3, g_buf_ptr, g_size);

      printf("first 4 bytes from guest: %08x\n", *((u32*)buf));
      
      /* Return to the _next_ instruction */
      linux_vmcb->rip += 3;
      break;
    }
    /* VISOR_DBG_STR passes a length and a pointer to a string. print
     * it via serial port. */
      case VISOR_DBG_STR:
      {
          u32 g_size; /* guest passes actual size; not pointer to size as in get */
          u32 g_buf_ptr;
          u8 buf[TMP_SIZE];
          printf("VISOR_DBG_STR ");
          /* actual size in ebx */
          g_size = REG_RD(3, gregs);
          printf("g_size %d ", g_size);
          /* buf ptr in ecx */
          g_buf_ptr = REG_RD(1, gregs);
          printf("g_buf_ptr %08x\n", g_buf_ptr);

          if(g_size > TMP_SIZE) {
              printf("ERROR: g_size (%d) > TMP_SIZE (%d); using TMP_SIZE\n",
                     g_size, TMP_SIZE);
              g_size = TMP_SIZE;
          }
          
          copy_from_guest(buf, (u64)linux_vmcb->cr3, g_buf_ptr, g_size);

          /* forcibly NULL-terminate just in case */
          buf[TMP_SIZE-1] = '\0';
          
          printf("VISOR_DBG_STR: %s\n", buf);
          
          /* Return to the _next_ instruction */
          linux_vmcb->rip += 3;
          break;
      }
  default:
    printf("FATAL ERROR: Invalid vmmcall cmd (%d)\n", cmd);
    FORCE_CRASH();
  }
  return;
}

void handle_npf(void)
{
  u32 ret;

  ret = scode_npf((u32)linux_vmcb->exitinfo2, (u64)linux_vmcb->exitinfo1, linux_vmcb->cr3);
  switch (ret)
  {
  case 0:
    /* pseodu page fault canceled by nested paging */
    linux_vmcb->eventinj.bytes = (u64)0;
    break;
  default:
    printf("FATAL ERROR: Unexpected return value from page fault handling\n");
    FORCE_CRASH();
  }

  return;
}

/* get a specific byte for an instruction in guest address space */
static inline u8 DECODE_INST_NB(u32 index)
{
  u32 tmp;					
  u8 *addr;					
  if (linux_vmcb->cr0 & CR0_PG)						
    tmp = guest_pt_walker(linux_vmcb->cr3, (u32)(linux_vmcb->rip) + index);    
  else						
    tmp = (u32)(linux_vmcb->cs.base) + (u32)(linux_vmcb->rip) + index; 
  addr = (u8 *)__gpa2hva(tmp);			
  return (*addr);
}

/* decode information for invlpg instruction */
#define DECODE_INVLPG_REG(mod, regnum)		\
	({					\
            u8 value;				\
	    value = DECODE_INST_NB(2);		\
	    mod = ((value) >> 6) & 0x3;		\
	    regnum = (value) & 0x7;		\
	})

#define DECODE_INVLPG_OFF(off)			\
	({					\
	    off = DECODE_INST_NB(3);		\
	})

/* decode information for crn instruction */
#define DECODE_CRN_REG(regnum)			\
	({					\
            u8 value;				\
	    value = DECODE_INST_NB(2);		\
	    regnum = (value) & 0x7;		\
	})


/* helper function to process msr intercept */
void update_msr(u32 op, u32 msr, u32 eax, u32 edx)
{
  u64 value = ((u64)edx << 32) | (u64)eax;

  if (op == 1)
  {
    switch (msr)
    {
    default:
      /* we catch all the write attemps to vm related msr here */
      printf("SECURITY: Unexpected writes to VM related msr (%x), value %llx\n", msr, value);
      FORCE_CRASH();
    }
  }
}

/* handler to process msr intercept */
void handle_msr(struct regs *greg)
{
  u32 *gregs = (u32 *)greg;
  u32 eax, edx, ecx;

  /* we don't intercept any msr read operation */
  if (linux_vmcb->exitinfo1 == 0) 
  {
    printf("FATAL ERROR: Unexpected msr read intercept\n");
    FORCE_CRASH();
  }

  eax = REG_RD(0, gregs);  
  edx = REG_RD(2, gregs);  
  ecx = REG_RD(1, gregs);  

  /* to access some information in VMCB, we must perform a vmsave
   * first, more details reference AMD manual
   */
  vmsave(__pa((u32)linux_vmcb));
  update_msr(1, ecx, eax, edx);
  /* to update some information in VMCB, we must perform a vmload 
   * finally, more details reference AMD manual
   */
  vmload(__pa((u32)linux_vmcb));

  linux_vmcb->rip += 2;
}

/* handler for protecting DEV conf from modification */ 
void verify_ioio(void)
{ 
  pci_config_reg_addr_t pci_addr; 

  /* read address from CONFIG_ADDR_PORT */
  pci_addr.bytes = inl((u32)CONFIG_ADDR_PORT);

  if ((pci_addr.fields.bus == DEV_BUS) && 
      (pci_addr.fields.device == DEV_DEVICE) && 
      (pci_addr.fields.function == DEV_FUNCTION))
  {
    if ((pci_addr.fields.offset >= dev_capoff) && 
        (pci_addr.fields.offset < dev_capoff + DEV_DATA + 4))
    {
      printf("SECURITY: Invalid write to DEV configuration space\n");
      FORCE_CRASH();
    }
  }
}

/* handler to process io intercept */
void handle_ioio(void)
{
  ioio_info_t ioinfo;
  
  ioinfo.bytes = linux_vmcb->exitinfo1;

  if (ioinfo.fields.rep || ioinfo.fields.str)
  {
    /* we don't support some repeated or string based access to PCI 
     * configuration space until now
     */
    printf("FATAL ERROR: Unsupported IO batch operations for PCI configuration space\n");
    FORCE_CRASH();
  }

  if (ioinfo.fields.type)
  {
    /* IN */
#if 0
      printf("DEBUG: ioio IN :");
#endif
    if (ioinfo.fields.sz8)
      *(u8 *)&linux_vmcb->rax = inb(ioinfo.fields.port);
    if (ioinfo.fields.sz16)
      *(u16 *)&linux_vmcb->rax = inw(ioinfo.fields.port);
    if (ioinfo.fields.sz32) 
       *(u32 *)&linux_vmcb->rax = inl(ioinfo.fields.port);
  }else
  {
    /* OUT */
    verify_ioio();
#if 0
      printf("DEBUG: ioio OUT:");
#endif
    if (ioinfo.fields.sz8)
      outb((u8)linux_vmcb->rax, ioinfo.fields.port);
    if (ioinfo.fields.sz16)
      outw((u16)linux_vmcb->rax, ioinfo.fields.port);
    if (ioinfo.fields.sz32) 
      outl((u32)linux_vmcb->rax, ioinfo.fields.port);
  }
#if 0
    {
      pci_config_reg_addr_t pci_addr; 

      /* read address from CONFIG_ADDR_PORT */
      pci_addr.bytes = inl((u32)CONFIG_ADDR_PORT);
    
      if (ioinfo.fields.sz8)
        printf(" value %#x, bus %#x dev %#x fun %#x off %#x\n", (u8)linux_vmcb->rax, pci_addr.fields.bus, pci_addr.fields.device, pci_addr.fields.function, pci_addr.fields.offset);
      if (ioinfo.fields.sz16)
        printf(" value %#x, bus %#x dev %#x fun %#x off %#x\n", (u16)linux_vmcb->rax, pci_addr.fields.bus, pci_addr.fields.device, pci_addr.fields.function, pci_addr.fields.offset);
      if (ioinfo.fields.sz32) 
        printf(" value %#x, bus %#x dev %#x fun %#x off %#x\n", (u32)linux_vmcb->rax, pci_addr.fields.bus, pci_addr.fields.device, pci_addr.fields.function, pci_addr.fields.offset);
    }
#endif
  /* the exitinfo2 store the rip of instruction following the IN/OUT */
  linux_vmcb->rip = linux_vmcb->exitinfo2;
}
