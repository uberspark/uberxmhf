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

/**
 * malloc.h - Provide memory allocation / freeing to the SLB.  This
 * will execute on physical addresses, which entails some special
 * handling of global variables and string literals.
 * edited by Zongwei Zhou
 */

/*
 * Maximum number of slots that can be allocated at one time
 */

/* Total memory that can theoretically be allocated at any time is:
 *   MEMORY_BUFFER_SIZE * 4 bytes
 */
#define TOTAL_MEM 4*1024*1024
#define MEMORY_BUFFER_SIZE (TOTAL_MEM>>2)

/* 
 * Number of bytes in each slot
 */
#define MEMORY_SLOT_SIZE 4 
#define TOTAL_SLOTS TOTAL_MEM/MEMORY_SLOT_SIZE


/* Bitset definitions */
#define Bitslot unsigned int
#define Bitset Bitslot *

/* Number of bits in a bitset slot
 * Currently, we use unsigned ints, so there are 32 bits/slot */
#define BITSET_SLOT_SIZE 32
#define BITSET_SLOT_ALL 0xFFFFFFFF

/* Number of slots in a bitset */
#define BITSET_SIZE (TOTAL_SLOTS/BITSET_SLOT_SIZE + 1)

/* Programmers get to define the meaning of truth */
#ifndef TRUE
#define TRUE 1
#endif

#ifndef FALSE
#define FALSE 0
#endif

#ifndef NULL
#define NULL 0
#endif

#ifndef bool
#define bool char
#endif



/***********************************************************************
 * Global Variable Declarations
 ***********************************************************************/

/* Pool of memory */
extern unsigned int memBuffer[MEMORY_BUFFER_SIZE];

/* Tracks which memory slots are available */
extern Bitslot memAvail[BITSET_SIZE];

/* Index i is set to 1 if it was allocated along with the previous slot */
extern Bitslot memContig[BITSET_SIZE];

/***********************************************************************
 * Global Function Declarations 
 ***********************************************************************/

void *static_malloc(unsigned int size);
void static_free(void* target);
int static_malloc_test(void); /* Controlled if #ifdef in malloc.c */

/***********************************************************************
 * File-Local Function Declarations (even though they are visible
 * globally)
 ***********************************************************************/

/* 
 * Initialize the memory regions
 */
void static_malloc_init(void);

/*
 * Find enough contiguous slots to allocate memory for this request 
 */
int findFreeSlots(int numSlots);

/*
 * Determines whether there are numSlots available starting at index
 */
bool checkContigSlots(int index, int numSlots);

/* 
 * Get the availability of memory slot i 
 */
bool getSlotAvail(int i);

/* 
 * Set the availability of memory slot i 
 */
void setSlotAvail(int i, bool avail);

/* 
 * Determine if this slot (slot i) is part of the previous slot
 */
bool getSlotContig(int i);

/* 
 * Adjust the continguity record of slot i
 */
void setSlotContig(int i, bool contig);

/*
 * Debug routine to display the bitmaps
 */
void printAvail(void);
void printContig(void);

/* Test whether a particular bit is set */
bool testBit(Bitset bits, int index); 

/* Set the value of a particular bit */
void setBit(Bitset bits, int index, bool val); 

/* Determine if there are any empty bits in the slot for the index indicated */
Bitslot testBitSlot(Bitset bits, int slotIndex);

/* Set all of the bits in the bitset (also need the length of the bitset) */
void bitsetSetAll(Bitset bits, int len); 

/* Clear all of the bits in the bitset (also need the length of the bitset) */
void bitsetClearAll(Bitset bits, int len);

