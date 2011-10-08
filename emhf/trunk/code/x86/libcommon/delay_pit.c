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

// delay.c
// implements micro/milli second delay based on 8254 Programmable
// interval timer. 
// author: amit vasudevan (amitvasudevan@acm.org)
// note: due to 8254 PIT usage, the routines in this module should not
// be called when a guest OS has been booted up on the physical PIT without
// saving/restoring the PIT registers

#include <emhf.h> 

//---microsecond delay----------------------------------------------------------
void udelay(u32 usecs){
  u8 val;
  u32 latchregval;  

  //enable 8254 ch-2 counter
  val = inb(0x61);
  val &= 0x0d; //turn PC speaker off
  val |= 0x01; //turn on ch-2
  outb(val, 0x61);
  
  //program ch-2 as one-shot
  outb(0xB0, 0x43);
  
  //compute appropriate latch register value depending on usecs
  latchregval = (1193182 * usecs) / 1000000;

  //write latch register to ch-2
  val = (u8)latchregval;
  outb(val, 0x42);
  val = (u8)((u32)latchregval >> (u32)8);
  outb(val , 0x42);
  
  //wait for countdown
  while(!(inb(0x61) & 0x20));
  
  //disable ch-2 counter
  val = inb(0x61);
  val &= 0x0c;
  outb(val, 0x61);
}
