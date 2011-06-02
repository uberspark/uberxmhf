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

/* 
 * Author - Jim Newsome (jnewsome@no-fuss.com)
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "sealed-code-pal-priv.h"
#include <stdio.h>
void scp_register(void)
{
  struct scode_params_info scp_params_info =
  {
    .params_num = 4,
    .pm_str =
    {
      {.type = SCODE_PARAM_TYPE_POINTER,
       .size = 1+sizeof(struct scp_in_msg)/(sizeof(int))}, /* FIXME rounding */
      {.type = SCODE_PARAM_TYPE_INTEGER,
       .size = 1},
      {.type = SCODE_PARAM_TYPE_POINTER,
       .size = 1+sizeof(struct scp_out_msg)/(sizeof(int))}, /* FIXME rounding */
      {.type = SCODE_PARAM_TYPE_POINTER,
       .size = 1},
    }
  };

  struct scode_sections_info scode_info;
  scode_sections_info_init(&scode_info,
                           sizeof(struct scp_in_msg)+sizeof(struct scp_out_msg)+PAGE_SIZE /* XXX fudge factor */,
                           2*PAGE_SIZE);
  scode_sections_info_print(&scode_info);
  fflush(NULL);
  assert(!scode_register(&scode_info, &scp_params_info, sealed_code_pal));
}

void scp_unregister(void)
{
  scode_unregister(sealed_code_pal);
}

size_t scp_sealed_size_of_unsealed_size(size_t in)
{
  return in + 80; /* FIXME: calculate this for real */
}

int scp_seal(uint8_t *incode, size_t incode_len, uint8_t *outcode, size_t *outcode_len)
{
  struct scp_in_msg *in;
  struct scp_out_msg *out;
  size_t out_len = sizeof(*out);
  
  assert((in = malloc(sizeof(struct scp_in_msg))) != NULL);
  assert((out = malloc(sizeof(struct scp_out_msg))) != NULL);

  /* XXX need to make sure these are swapped in,
     since we aren't necessarily writing to all of the
     pages inside.
  */
  scode_touch_range(in, sizeof(*in), 1);
  scode_touch_range(out, sizeof(*out), 1);

  in->command = SCP_SEAL;

  assert(incode_len <= SCP_MAX_UNSEALED_LEN);
  memcpy(in->m.seal.code, incode, incode_len);
  in->m.seal.code_len = incode_len;

  scp_register();
  sealed_code_pal(in, sizeof(*in), out, &out_len);
  scp_unregister();

  if(out->status != 0) {
    return out->status;
  }

  assert(out->r.seal.code_len <= *outcode_len);
  *outcode_len = out->r.seal.code_len;

  memcpy(outcode, out->r.seal.code, out->r.seal.code_len);

  return 0;
}

int scp_run(uint8_t *incode, size_t incode_len,
            uint8_t *params, size_t params_len,
            uint8_t *output, size_t *output_len)
{
  struct scp_in_msg *in;
  struct scp_out_msg *out;
  size_t out_len = sizeof(*out);

  assert((in = malloc(sizeof(struct scp_in_msg))) != NULL);
  assert((out = malloc(sizeof(struct scp_out_msg))) != NULL);

  /* XXX need to make sure these are swapped in,
     since we aren't necessarily writing to all of the
     pages inside.
  */
  scode_touch_range(in, sizeof(*in), 1);
  scode_touch_range(out, sizeof(*out), 1);

  in->command = SCP_LOAD;

  assert(incode_len <= SCP_MAX_SEALED_LEN);
  memcpy(in->m.load.code, incode, incode_len);
  in->m.load.code_len = incode_len;

  assert(params_len <= SCP_MAX_PARAM_LEN);
  memcpy(in->m.load.params, params, params_len);
  in->m.load.params_len = params_len;

  scp_register();
  sealed_code_pal(in, sizeof(*in), out, &out_len);
  scp_unregister();

  if(out->status != 0) {
    return out->status;
  }

  assert(out->r.load.output_len <= *output_len);
  *output_len = out->r.load.output_len;

  memcpy(output, out->r.load.output, out->r.load.output_len);

  return 0;
}
