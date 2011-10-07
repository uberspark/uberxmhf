#ifndef CBUF_H
#define CBUF_H

#include <stddef.h>

typedef struct {
  size_t sz;
  size_t readi;
  size_t writei;
  uint8_t buf[];
} cbuf_t;

cbuf_t* cbuf_init(void *buf, size_t sz);
size_t cbuf_readn(cbuf_t *cbuf, void *dst, size_t n);
size_t cbuf_writen(cbuf_t *cbuf, const void *src, size_t n);

#endif
