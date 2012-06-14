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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#include "pals.h" /* TODO: fix dependencies so this can go last */

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include <trustvisor/tv_utpm.h>

#include "libarbtools.h"

/*
 * if 'prefix' != NULL, print it before each line of hex string
 */
void print_hex(const char *prefix, const void *prtptr, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ ) {
        if ( i % 16 == 0 && prefix != NULL )
            printf("\n%s", prefix);
        printf("%02x ", *(const uint8_t *)prtptr++);
    }
    printf("\n");
}

/* Read entire file into a newly-allocated buffer. */
/* Returns positive integer representing number of bytes read, or
 * negative value on error.  Don't care about size 0 files. */
long slurp_file(const char *filename, void **buf) {
    if(!filename || !buf) return -1;

    FILE *fh = fopen(filename, "rb");
    if(NULL == fh) return -2;

    /* how big is the file? */
    fseek(fh, 0L, SEEK_END);
    long s = ftell(fh);
    rewind(fh);

    /* get some space for its bytes */
    *buf = malloc(s);
    if(NULL == *buf) {
        fclose(fh); fh = NULL;
        return -3;
    }

    fread(*buf, s, 1, fh);
    fclose(fh); fh = NULL;

    printf("  slurp_file successfully read %ld bytes from %s\n",
           s, filename);
    
    return s;
}

/* Create a file (clobbering any existing file) and write the contents
 * of 'bytes' to it. Returns the number of bytes written on success,
 * or a negative value on error. */
long puke_file(const char *filename, const void *bytes, long len) {
    if(!filename || !bytes || len < 1) return -1;

    FILE *fh = fopen(filename, "wb");
    if(NULL == fh) return -2;

    if(fwrite(bytes, len, 1, fh) != 1) return -3;
    fclose(fh); fh = NULL;

    printf("  puke_file successfully wrote %ld bytes to %s\n",
           len, filename);
    
    return len;
}

void dump_stderr_from_pal(tz_operation_t *tzOp) {
  tz_return_t tzRet;
  uint8_t *stderr_buf;
  size_t stderr_buf_len;
  char last;

  tzRet = TZIDecodeF(tzOp,
                     "%"TZI_DARRSPC,
                     &stderr_buf, &stderr_buf_len);
  if (tzRet) {
    printf("[ERROR] PAL's stderr unavailable. tzRet = %d\n", tzRet);
    return;
  }

  /* Take care to NULL-terminate the string */
  last = stderr_buf[stderr_buf_len-1];
  stderr_buf[stderr_buf_len-1] = '\0'; 
  printf("********************* BEGIN PAL's STDERR ****************************************\n");
  printf("%s%c%s", stderr_buf, last, last == '\n' ? "" : "\n");
  printf("********************* END PAL's STDERR ******************************************\n");
}
