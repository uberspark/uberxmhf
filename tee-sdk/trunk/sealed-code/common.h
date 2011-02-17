#ifndef COMMON_H
#define COMMON_H

#include <stdint.h>

int read_file(char *path, uint8_t **data);
int write_file(char *path, uint8_t *data, size_t data_len);

#endif
