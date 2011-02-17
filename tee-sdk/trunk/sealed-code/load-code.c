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
