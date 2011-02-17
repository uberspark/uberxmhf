#include <assert.h>
#include <stdio.h>
#include <sys/stat.h>
#include <stdlib.h>
#include "common.h"


int read_file(char *path, uint8_t **data)
{
  struct stat st;
  FILE *f = NULL;
  int len;
  int rv;

  assert(!stat(path, &st));
  len = st.st_size;

  assert((*data = malloc(len)) != NULL);

  assert((f = fopen(path, "r")) != NULL);
  assert((rv = fread(*data, 1, len, f)) == len);
  assert(!fclose(f));
  
  return len;
}

int write_file(char *path, uint8_t *data, size_t data_len)
{
  FILE *f = NULL;

  assert((f = fopen(path, "w")) != NULL);
  assert(fwrite(data, 1, data_len, f) == data_len);
  assert(!fclose(f));

  return 0;
}

