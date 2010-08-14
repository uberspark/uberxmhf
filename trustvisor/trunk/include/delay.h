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

/* io.h Functions to read and write I/O ports on x86
 * Modified from Xen for Visor by Elaine Shi and Arvind Seshadri
 */ 
#ifndef __DELAY_H_
#define __DELAY_H_

#ifndef __ASSEMBLY__


static inline void simhost_delay(u64 count)
{
	if (count)
		while (count --);
}

#define simhost_udelay(n)	simhost_delay(n * 3000)

static inline void delay(u64 count)
{
	if (count)
		while (count --);
}

#define e1000_udelay(n)	delay(n * 3000)
#define e1000_mdelay(n)	delay(n * 3000000)
#define e1000_msleep(n)	delay(n * 5000000)


#define LOCKDOWN_TIMEOUT_1MS	((0x40000000ULL * 2) / 1000)

static inline void mdelay(unsigned int msec)
{
/* first value is 1GHz,
 * second is seconds to wait
 * the third one depends how fast your CPU is 
 */
	unsigned long long cycles = LOCKDOWN_TIMEOUT_1MS * msec;
	unsigned long long diff;
	unsigned int lo_before, hi_before, lo_after, hi_after;

	__asm__ __volatile__ ("rdtsc" : "=a" (lo_before), "=d"(hi_before));
	do 
	{
		__asm__ __volatile__ ("rdtsc" : "=a" (lo_after), "=d"(hi_after));
		diff = (((unsigned long long)hi_after << 32) | lo_after) - (((unsigned long long)hi_before << 32) | lo_before);
	} while (diff < cycles);
}

static inline void simhost_mdelay(unsigned int msec)
{
/* first value is 1GHz,
 * second is seconds to wait
 * the third one depends how fast your CPU is 
 */
	unsigned long long cycles = LOCKDOWN_TIMEOUT_1MS * msec;
	unsigned long long diff;
	unsigned int lo_before, hi_before, lo_after, hi_after;

	__asm__ __volatile__ ("rdtsc" : "=a" (lo_before), "=d"(hi_before));
	do 
	{
		__asm__ __volatile__ ("rdtsc" : "=a" (lo_after), "=d"(hi_after));
		diff = (((unsigned long long)hi_after << 32) | lo_after) - (((unsigned long long)hi_before << 32) | lo_before);
	} while (diff < cycles);
}

#endif /* __ASSEMBLY__ */

#endif /* __DELAY_H_ */
