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

/* 
 * Author - Jim Newsome (jnewsome@no-fuss.com)
 */

#include <string.h>
#include <sys/stat.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "sealed-code-pal.h"
#include "common.h"

struct params_s
{
  char *sealed_code_filename;
  char *sealed_code_param;
};

int parse_args(int argc, char **argv, struct params_s *params)
{
  assert(argc >= 3);

  params->sealed_code_filename = argv[1];
  params->sealed_code_param = argv[2];
  return 0;
}

int main(int argc, char **argv)
{
  struct params_s params;
  uint8_t *sealed;
  size_t sealed_len;
  char output[SCP_MAX_OUTPUT_LEN/sizeof(char)];
  size_t output_len = sizeof(output);
  int rv;

  parse_args(argc, argv, &params);

  sealed_len = read_file(params.sealed_code_filename, &sealed);

  rv = scp_run(sealed, sealed_len,
               (uint8_t*)params.sealed_code_param, 1+strlen(params.sealed_code_param),
               (uint8_t*)output, &output_len);
  if (rv != 0) {
    printf("scp_run returned error %d\n", rv);
    exit(1);
  }

  printf("sealed function returned:\n%s\n", output);

  return 0;
}
