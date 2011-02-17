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
