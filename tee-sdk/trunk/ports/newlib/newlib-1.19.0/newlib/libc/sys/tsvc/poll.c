#include <poll.h>
#include <errno.h>

int   poll(struct pollfd fds[], nfds_t ndfs, int timeout)
{
  errno=ENOSYS;
  return -1;
}
