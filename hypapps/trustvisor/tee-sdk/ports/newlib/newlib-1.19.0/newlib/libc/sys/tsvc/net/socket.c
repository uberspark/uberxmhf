#include <sys/socket.h>
#include <errno.h>

int     accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{
  errno=ENOSYS;
  return -1;
}

int     bind(int sockfd, const struct sockaddr *addr, socklen_t addrlen)
{
  errno=ENOSYS;
  return -1;
}

int     connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen)
{
  errno=ENOSYS;
  return -1;
}

int     getpeername(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{
  errno=ENOSYS;
  return -1;
}

int     getsockname(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{
  errno=ENOSYS;
  return -1;
}

int     getsockopt(int sockfd, int level, int optname, void *optval, socklen_t *optlen)
{
  errno=ENOSYS;
  return -1;
}

int     listen(int sockfd, int backlog)
{
  errno=ENOSYS;
  return -1;
}

ssize_t recv(int sockfd, void *buf, size_t len, int flags)
{
  errno=ENOSYS;
  return -1;
}

ssize_t recvfrom(int sockfd, void *buf, size_t len, int flags,
                 struct sockaddr *src_addr, socklen_t *addrlen)
{
  errno=ENOSYS;
  return -1;
}

ssize_t recvmsg(int sockfd, struct msghdr *msg, int flags)
{
  errno=ENOSYS;
  return -1;
}

ssize_t send(int sockfd, const void *buf, size_t len, int flags)
{
  errno=ENOSYS;
  return -1;
}

ssize_t sendmsg(int sockfd, const struct msghdr *msg, int flags)
{
  errno=ENOSYS;
  return -1;
}

ssize_t sendto(int sockfd, const void *buf, size_t len, int flags,
               const struct sockaddr *dest_addr, socklen_t addrlen)
{
  errno=ENOSYS;
  return -1;
}

int     setsockopt(int sockfd, int level, int optname,
                   const void *optval, socklen_t optlen)
{
  errno=ENOSYS;
  return -1;
}

int     shutdown(int sockfd, int how)
{
  errno=ENOSYS;
  return -1;
}

int     socket(int domain, int type, int protocol)
{
  errno=ENOSYS;
  return -1;
}

int     sockatmark(int sockfd)
{
  errno=ENOSYS;
  return -1;
}

int     socketpair(int domain, int type, int protocol, int sv[2])
{
  errno=ENOSYS;
  return -1;
}
