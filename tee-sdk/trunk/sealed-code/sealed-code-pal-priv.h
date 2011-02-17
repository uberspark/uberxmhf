#ifndef SEALED_CODE_PAL_PRIV_H
#define SEALED_CODE_PAL_PRIV_H

#include <scode.h>
#include "sealed-code-pal.h"

/* addresses of these will be set by linker */
extern unsigned int __scode_start, __scode_end, __sdata_start, __sdata_end;

enum scp_command_t {
  SCP_SEAL=0,
  SCP_LOAD=1,
};

struct scp_in_msg {
  enum scp_command_t command;
  union {
    struct {
      uint8_t code[SCP_MAX_UNSEALED_LEN];
      size_t code_len;
    } seal;
    struct {
      uint8_t code[SCP_MAX_SEALED_LEN];
      size_t code_len;
      uint8_t params[SCP_MAX_PARAM_LEN];
      size_t params_len;
    } load;
  } m;
};

struct scp_out_msg {
  uint32_t status;
  /* when status == 0, returned msg has the
   * same type as input command. Otherwise undefined.
   */
  union {
    struct {
      uint8_t code[SCP_MAX_SEALED_LEN];
      size_t code_len;
    } seal;
    struct {
      uint8_t output[SCP_MAX_OUTPUT_LEN];
      size_t output_len;
    } load;
  } r;
};

void scp_entry(struct scp_in_msg *in, size_t in_len,
               struct scp_out_msg *out, size_t *out_len);

#endif
