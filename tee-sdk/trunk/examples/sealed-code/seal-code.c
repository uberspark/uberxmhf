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

/* Copyright 2011, NoFuss Security, Inc.
 * Author - Jim Newsome (jnewsome@no-fuss.com)
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "sealed-code-pal.h"
#include "common.h"

struct params_s
{
  char *inf;
  char *outf;
};

int parse_args(int argc, char **argv, struct params_s *params)
{
  params->inf = argv[1];
  params->outf = argv[2];
  return 0;
}

int main(int argc, char **argv)
{
  struct params_s params;
  uint8_t *indata;
  int indata_len;
  uint8_t *outdata;
  size_t outdata_len;
  int rv;

  parse_args(argc, argv, &params);

  indata_len = read_file(params.inf, &indata);

  outdata_len = scp_sealed_size_of_unsealed_size(indata_len);
  assert((outdata = malloc(outdata_len)) != NULL);
  
  rv = scp_seal(indata, indata_len, outdata, &outdata_len);
  if (rv != 0) {
    printf("scp_seal returned error %d\n", rv);
    exit(1);
  }

  write_file(params.outf, outdata, outdata_len);

  return 0;
}
