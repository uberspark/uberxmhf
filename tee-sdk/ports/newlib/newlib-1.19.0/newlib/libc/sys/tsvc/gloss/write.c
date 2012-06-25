#include <stdint.h>
#include <stdbool.h>
#include <unistd.h>
#include <errno.h>
#include "cbuf.h"

static uint8_t stderr_buf[4096];
static cbuf_t *stderr_cbuf = ((cbuf_t*)stderr_buf);

ssize_t write(int fd, const void *buf, size_t count)
{
  static bool initd_stderr;
  if (!initd_stderr) {
    cbuf_init(stderr_buf, 4096);
    initd_stderr=true;
  }

  if (fd == STDERR_FILENO) {
    return cbuf_writen(stderr_cbuf, buf, count);
  } else {
    errno=EBADF;
    return -1;
  }
}

size_t tsvc_read_stderr(void *buf, size_t count)
{
  return cbuf_readn(stderr_cbuf, buf, count);
}
