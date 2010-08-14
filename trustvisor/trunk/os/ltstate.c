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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PAGE_SIZE 0x1000

/* TODO: Centralize these definitions somewhere */
enum VisorScmd
{
  VISOR_SCMD_REG = 1,
  VISOR_SCMD_UNREG = 2,
  VISOR_STPM_PCRREAD = 11,
  VISOR_STPM_EXTEND = 12,
  VISOR_STPM_SEAL = 13,
  VISOR_STPM_UNSEAL = 14,
  VISOR_STPM_QUOTE = 15,
  VISOR_STPM_RAND = 16,
  //  VISOR_STPM_GETPUBKEY = 17,
  VISOR_LTSTATE_GETSIZE = 100,
  VISOR_LTSTATE_GET = 101,
  VISOR_LTSTATE_PUT = 102,
  VISOR_DBG_STR = 200,
};


static inline void dump_bytes(unsigned char *bytes, int len)
{
    int i;
    if(!bytes) return;

    for (i=0; i<len; i++) {
        printf("%02x",bytes[i]);
        if(i>0 && !((i+1)%16)) {
            printf("\n");
        } else {
            printf(" ");
        }
    }
    if(len%16) {
        printf("\n");
    }
}

/**
 * Asl TrustVisor how big its long-term state is, so that the
 * appropriate amount of memory can be allocated prior to calling
 * ltstate_get.
 */
int ltstate_getsize(unsigned int *size)
{
	int ret;

	printf("About to make vmmcall(VISOR_LTSTATE_GETSIZE %p)\n", size);
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_LTSTATE_GETSIZE), "b"(size));

	printf("After vmmcall, ret %d\n", ret);
    return ret;
}

/**
 * Request that TrustVisor encrupt its long-term (i.e., must survive a
 * boot-cycle) state using TPM_Seal, and return the resulting
 * ciphertext.  *size may be preassigned with the maximum size of buf,
 * so that TrustVisor will not overrun buf.
 */
int ltstate_get(unsigned int *size, unsigned char *buf)
{
	int ret;

	printf("About to make vmmcall(VISOR_LTSTATE_GET %p %p)\n", size, buf);
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_LTSTATE_GET), "b"(size), "c"(buf));

	printf("After vmmcall, ret %d\n", ret);
    return ret;
}

/**
 * Inject previously received data from a call to ltstate_get. 
 */
int ltstate_put(unsigned int size, unsigned char *buf)
{
	int ret;

	printf("About to make vmmcall(VISOR_LTSTATE_PUT %p %p)\n", size, buf);
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_LTSTATE_PUT), "b"(size), "c"(buf));

	printf("After vmmcall, ret %d\n", ret);
    return ret;
}


/**
 * Print a debug message via the hypervisor's serial debug facility
 */
int _dbg_str(char *str, unsigned int size)
{
	int ret;

	printf("About to make vmmcall(VISOR_DBG_STR %p %p)\n", size, str);
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_DBG_STR), "b"(size), "c"(str));

	printf("After vmmcall, ret %d\n", ret);
    return ret;
}

int dbg_str(char *str) {
    _dbg_str(str, strlen(str)+1);
}

int main(int argc, char *argv) {
    int i, size = 2048;
    unsigned char buf[2048];
    char *msg = "The quick brown FOX jumped over the lazy DOG.";

    ltstate_getsize(&size);
    printf("ltstate_getsize ret %d\n", size);    
    
    ltstate_get(&size, buf);

    printf("new size %d\n", size);
    dump_bytes(buf, size);

    /* Modify the data */
    for(i=0; i<size; i++) buf[i]++;
    
    ltstate_put(size, buf);

    dbg_str(msg);
    
    return 0;
}
