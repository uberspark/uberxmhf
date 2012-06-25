#include <string.h>
#include <stddef.h>
#include <stdint.h>
#include "cbuf.h"

cbuf_t* cbuf_init(void *buf, size_t sz)
{
  cbuf_t *rv = (cbuf_t*)buf;
  *rv = (cbuf_t) {
    .sz=sz-sizeof(cbuf_t),
    .readi=0,
    .writei=0,
  };
}

#define MAX(x, y) (((y) > (x)) ? (y) : (x))

static size_t cbuf_read(cbuf_t *cbuf, void *dst)
{
  size_t numread=0;

  if (cbuf->readi == cbuf->writei) {
    return 0; /* empty */
  } else {
    *((uint8_t*)dst) = cbuf->buf[cbuf->readi];
    cbuf->readi = (cbuf->readi + 1) % cbuf->sz;
    return 1;
  }
}

static size_t cbuf_write(cbuf_t *cbuf, const void *src)
{
  size_t numread=0;

  if ((cbuf->writei+1)%cbuf->sz == (cbuf->readi)) {
    return 0; /* full */
  } else {
    cbuf->buf[cbuf->writei] = *((const uint8_t*)src);
    cbuf->writei = (cbuf->writei + 1) % cbuf->sz;
    return 1;
  }
}

size_t cbuf_readn(cbuf_t *cbuf, void *dst, size_t n)
{
  size_t numread=0;

  while(numread < n) {
    if (0 == cbuf_read(cbuf, &((uint8_t*)dst)[numread])) {
      return numread;
    } else {
      numread++;
    }
  }
  return numread;
}

size_t cbuf_writen(cbuf_t *cbuf, const void *src, size_t n)
{
  size_t numwritten=0;

  while(numwritten < n) {
    if (0 == cbuf_write(cbuf, &((const uint8_t*)src)[numwritten])) {
      return numwritten;
    } else {
      numwritten++;
    }
  }
  return numwritten;
}
