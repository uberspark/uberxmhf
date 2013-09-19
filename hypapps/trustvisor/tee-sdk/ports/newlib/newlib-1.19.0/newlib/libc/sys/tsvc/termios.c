#include <termios.h>
#include <unistd.h>
#include <errno.h>

speed_t cfgetispeed(const struct termios *termios_p)
{
  return termios_p->c_ispeed;
}
speed_t cfgetospeed(const struct termios *termios_p)
{
  return termios_p->c_ospeed;
}

int     cfsetispeed(struct termios *termios_p, speed_t speed)
{
  termios_p->c_ispeed = speed;
  return 0;
}

int     cfsetospeed(struct termios *termios_p, speed_t speed)
{
  termios_p->c_ospeed = speed;
  return 0;
}

int     tcdrain(int fd)
{
  errno = ENOSYS;
  return -1;
}

int     tcflow(int fd, int action)
{
  errno = ENOSYS;
  return -1;
}

int     tcflush(int fd, int queue_selector)
{
  errno = ENOSYS;
  return -1;
}

int     tcgetattr(int fd, struct termios *termios_p)
{
  errno = ENOSYS;
  return -1;
}

/* pid_t   tcgetsid(int fd) */
/* { */
/*   errno = ENOSYS; */
/*   return -1; */
/* } */

int     tcsendbreak(int fd, int duration)
{
  errno = ENOSYS;
  return -1;
}

int     tcsetattr(int fd, int optional_actions,
                  const struct termios *termios_p)
{
  errno = ENOSYS;
  return -1;
}
