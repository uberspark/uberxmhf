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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

//xmhfhw_cpu_legio: CPU Legacy IO functions
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>


__attribute__((naked)) void outl(u32 val, u32 port){
    asm volatile ("movl 0x4(%esp), %eax \r\n"); //eax = val
    asm volatile ("movl 0x8(%esp), %edx \r\n"); //edx = port
    asm volatile ("outl %eax, %dx \r\n"); //output eax to dx
    asm volatile ("ret \r\n");
//    asm__ __volatile__("out %0, %w1"
//         :
//         :"a"(val), "Nd"((u16)port));
}

__attribute__((naked)) void outw (u32 value, u32 port){
    asm volatile ("movl 0x4(%esp), %eax \r\n"); //eax = val
    asm volatile ("movl 0x8(%esp), %edx \r\n"); //edx = port
    asm volatile ("outw %ax, %dx \r\n"); //output ax to dx
    asm volatile ("ret \r\n");

//  __asm__ __volatile__ ("outw %w0,%w1": :"a" ((u16)value), "Nd" ((u16)port));
}

__attribute__((naked)) void outb (u32 value, u32 port){
    asm volatile ("movl 0x4(%esp), %eax \r\n"); //eax = val
    asm volatile ("movl 0x8(%esp), %edx \r\n"); //edx = port
    asm volatile ("outb %al, %dx \r\n"); //output al to dx
    asm volatile ("ret \r\n");

//  __asm__ __volatile__ ("outb %b0,%w1": :"a" ((u8)value), "Nd" ((u16)port));
}

__attribute__((naked)) u32 inl(u32 port){
    asm volatile ("movl 0x4(%esp), %edx \r\n"); //edx = port
    asm volatile ("xorl %eax, %eax \r\n");
    asm volatile ("inl %dx, %eax \r\n");
    asm volatile ("xorl %edx, %edx \r\n");
    asm volatile ("ret \r\n");

/*  u32 val;

  __asm__ __volatile__("in %w1, %0"
               :"=a"(val)
               :"Nd"((u16)port));
  return val;*/
}

__attribute__((naked)) u16 inw (u32 port){

/*  u16 _v;

  __asm__ __volatile__ ("inw %w1,%0":"=a" (_v):"Nd" ((u16)port));
  return _v;*/
    asm volatile ("movl 0x4(%esp), %edx \r\n"); //edx = port
    asm volatile ("xorl %eax, %eax \r\n");
    asm volatile ("inw %dx, %ax \r\n");
    asm volatile ("xorl %edx, %edx \r\n");
    asm volatile ("ret \r\n");

}

__attribute__((naked)) u8 inb (u32 port){
/*  u8 _v;

  __asm__ __volatile__ ("inb %w1,%0":"=a" (_v):"Nd" ((u16)port));
  return _v;*/

    asm volatile ("movl 0x4(%esp), %edx \r\n"); //edx = port
    asm volatile ("xorl %eax, %eax \r\n");
    asm volatile ("inb %dx, %al \r\n");
    asm volatile ("xorl %edx, %edx \r\n");
    asm volatile ("ret \r\n");

}

