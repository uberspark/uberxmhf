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

/* drivers/vga.c: Low-level functions for writing to display
 * Modified from Xen's vga.c for TrustVisor by Elaine Shi and 
 * Arvind Seshadri
 */

#include <types.h>
#include <string.h>
#include <io.h>
#include <svm.h>
#include <visor.h>

static u32 xpos, ypos;
static u32 video;
static u32 vgacon_enabled = 1;

static int detect_video(u32 video_base) __attribute__ ((section ("_init_text")));
static int detect_vga(void) __attribute__ ((section ("_init_text")));
void init_vga(void) __attribute__ ((section ("_init_text")));

/* VGA text (mode 3) definitions. */
#define COLUMNS     80
#define LINES       25
#define ATTRIBUTE    7

/* Clear the screen and initialize VIDEO, XPOS and YPOS.  */

static void cls(void)
{
  memset((char *)video, 0, COLUMNS * LINES * 2);
  xpos = ypos = 0;
  outw(10 + (1 << (5 + 8)), 0x3d4); // cursor off
}

static int detect_video(u32 video_base)
{
  volatile u16 *p = (volatile u16 *)video_base;
  u16 saved1 = p[0], saved2 = p[1];
  int video_found = 1;

  p[0] = 0xAA55;
  p[1] = 0x55AA;
  if ( (p[0] != 0xAA55) || (p[1] != 0x55AA) )
    video_found = 0;

  p[0] = 0x55AA;
  p[1] = 0xAA55;
  if ( (p[0] != 0x55AA) || (p[1] != 0xAA55) )
    video_found = 0;

  p[0] = saved1;
  p[1] = saved2;

  return video_found;
}

static int detect_vga(void)
{
  /*   Look at a number of well-known locations. Even if video is not at */
  /*   0xB8000 right now, it will appear there when we set up text mode 3. */
    
  /*   We assume if there is any sign of a video adaptor then it is at least */
  /*   VGA-compatible (surely no one runs CGA, EGA, .... these days?). */
     
  /*   These checks are basically to detect headless server boxes. */
   return (detect_video(__va(0xA0000)) || 
	   detect_video(__va(0xB0000)) || 
	   detect_video(__va(0xB8000)));
}

/* This is actually code from vgaHWRestore in an old version of XFree86 :-) */
void init_vga(void)
{
  /* The following VGA state was saved from a chip in text mode 3. */
  static unsigned char regs[] = {
    /* Sequencer registers */
    0x03, 0x00, 0x03, 0x00, 0x02,
    /* CRTC registers */
    0x5f, 0x4f, 0x50, 0x82, 0x55, 0x81, 0xbf, 0x1f, 0x00, 0x4f, 0x20,
    0x0e, 0x00, 0x00, 0x01, 0xe0, 0x9c, 0x8e, 0x8f, 0x28, 0x1f, 0x96,
    0xb9, 0xa3, 0xff,
    /* Graphic registers */
    0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x0e, 0x00, 0xff,
    /* Attribute registers */
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x14, 0x07, 0x38, 0x39, 0x3a,
    0x3b, 0x3c, 0x3d, 0x3e, 0x3f, 0x0c, 0x00, 0x0f, 0x08, 0x00
  };

  int i, j = 0;
  volatile unsigned char tmp;

  if ( !vgacon_enabled )
    return;

  if ( !detect_vga() )
  {
    vgacon_enabled = 0;
    return;
  }


  video = __va(0xB8000);

  tmp = inb(0x3da);
  outb(0x00, 0x3c0);
  
  for ( i = 0; i < 5;  i ++ )
    outw((u32)(regs[j ++] << 8) | i, 0x3c4);
  
  /* Ensure CRTC registers 0-7 are unlocked by clearing bit 7 of CRTC[17]. */
  outw((u32)((regs[5+17] & 0x7F) << 8) | 17, 0x3d4);
  
  for ( i = 0; i < 25; i ++ ) 
    outw((u32)(regs[j ++] << 8) | i, 0x3d4);
  
  for ( i = 0; i < 9;  i ++ )
    outw((u32)(regs[j ++] << 8) | i, 0x3ce);
  
  for ( i = 0; i < 21; i ++ )
  {
    tmp = inb(0x3da);
    outb((u32)i, 0x3c0); 
    outb(regs[j ++], 0x3c0);
  }
  
  tmp = inb(0x3da);
  outb(0x20, 0x3c0);

  cls();
}

static void put_newline(void)
{
  xpos = 0;
  ypos ++;

  if (ypos >= LINES)
  {
    static char zeroarr[2 * COLUMNS] = { 0 };
    ypos = LINES - 1;
    memcpy((char*)video, 
           (char*)video + 2 * COLUMNS, (LINES - 1) * 2 * COLUMNS);
    memcpy((char*)video + (LINES - 1) * 2 * COLUMNS, 
           zeroarr, 2 * COLUMNS);
  }
}

static void putchar_console(int c)
{
  if ( !vgacon_enabled )
    return;

  if ( c == '\n' )
  {
    put_newline();
  }
  else
  {
    unsigned char *video_buf = (unsigned char *)video;
    video_buf[(xpos + ypos * COLUMNS) * 2]     = c & 0xFF;
    video_buf[(xpos + ypos * COLUMNS) * 2 + 1] = ATTRIBUTE;
    if ( ++ xpos >= COLUMNS )
      put_newline();
  }
}

/* print newline containing null terminated strings */
void putstr(const char *str)
{
  int c;

  while ( (c = *str ++) != '\0' )
    putchar_console(c);
}
