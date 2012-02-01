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

OUTPUT_ARCH(i386)

ENTRY(_sl_start)

/* Goal: constrain the size of the trusted portion of the SL to 64K. AMD
 * systems limit the Secure Loader Block to 64K max.  Intel permits a   
 * larger MLE (their name for SLB), but we want to remain compatible
 * with both.
 */

/* Useful reference:
 * http://docs.redhat.com/docs/en-US/Red_Hat_Enterprise_Linux/4/html/Using_ld_the_GNU_Linker/memory.html
 */

MEMORY
{
  low  (rwxai) : ORIGIN = 0,   LENGTH = 64K
  high (rwxai) : ORIGIN = 64K, LENGTH = 1984K /* balance of 2M total */ 
  unaccounted (rwxai) : ORIGIN = 0, LENGTH = 0 /* see section .unaccounted at end */
}

              
SECTIONS
{
  . = 0x00000000;
  .sl_header : {
    *(.sl_header)
    . = ALIGN(4096);    
  } >low

  .text : {
    *(.text)
  } >low

  .data : {
    *(.data)
  } >low

  .rodata : {
    *(.rodata)
  } >low

  /* discard? */
  .eh_frame : {
    *(.eh_frame)
  } >low

  .bss : {
    *(.bss)
    /*. = ALIGN(4096);*/    
    . = ALIGN(16);    
  } >low

	/* protected DMA protection buffer for DMA protection boot-strapping */
	/*.protdmabuffer : {
		*(.protdmabuffer)
	} >low*/

  .sl_stack : {
    *(.sl_stack)
    . = ALIGN(0x10000);
  } >low

  /* Content below is UNTRUSTED.
   * SL *MUST* sanitize any data here prior to use!
   */
  .sl_untrusted_params : {
    *(.sl_untrusted_params)
    *(.comment)
    . = ALIGN(0x200000);
  } >high

  /* this is to cause the link to fail if there is
   * anything we didn't explicitly place.
   * when this does cause link to fail, temporarily comment
   * this part out to see what sections end up in the output
   * which are not handled above, and handle them.
   */
  .unaccounted : {
    *(*)
  } >unaccounted
}
