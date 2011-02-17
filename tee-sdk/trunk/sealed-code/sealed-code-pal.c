/* TV */
#include <scode.h>

/* local */
#include "sealed-code-pal-priv.h"

static struct {
  uint8_t unsealed[SCP_MAX_UNSEALED_LEN]; /* XXX overloading this macro. XXX need to set up storage for this and make it executable */
} pal_static __attribute__ ((section(".sdata"))) = {{0}};

__attribute__ ((section (".scode")))
static int do_seal(uint8_t *unsealed, size_t unsealed_len,
                   uint8_t *sealed, size_t *sealed_len)
{
  return scode_seal(NULL, /* use current PCR value */
                    unsealed, unsealed_len,
                    sealed, sealed_len);
}

__attribute__ ((section (".scode")))
static int do_load(uint8_t *code, size_t code_len,
                   uint8_t *params, size_t params_len,
                   uint8_t *output, size_t *output_len)
{
  size_t unsealed_len = sizeof(pal_static.unsealed);
  scp_sealed_fn_t fn = (scp_sealed_fn_t)pal_static.unsealed;
  int rv;
  
  if((rv = scode_unseal(code, code_len,
                        pal_static.unsealed, &unsealed_len))) {
    return rv;
  }

  /* XXX Check source of sealed data? unseal api doesn't currently allow this */

  /* XXX make sure code pages are executable? */
  /* XXX perhaps extend one of the PCRs first? */

  fn(params, params_len, output, output_len);

  return 0;
}

__attribute__ ((section (".scode")))
void scp_entry(struct scp_in_msg *in, size_t in_len,
               struct scp_out_msg *out, size_t *out_len)
{
  if (in_len < sizeof(*in)) {
    out->status = -1;
    return;
  }
  if (*out_len < sizeof(*out)) {
    out->status = -2;
    return;
  }
  if ((uintptr_t)in == (uintptr_t)out) {
    /* XXX really ought to check more comprehensively for overlap */
    out->status = -3;
    return;
  }
  
  switch(in->command) {
  case SCP_SEAL:
    out->status = do_seal(in->m.seal.code, in->m.seal.code_len,
                          out->r.seal.code, &out->r.seal.code_len);
    break;
  case SCP_LOAD:
    out->r.load.output_len = sizeof(out->r.load.output);
    out->status = do_load(in->m.load.code, in->m.load.code_len,
                          in->m.load.params, in->m.load.params_len,
                          out->r.load.output, &out->r.load.output_len);
    break;
  default:
    out->status = -4;
  }
}
