/* based on IEEE Std 1003.1-2008
 * http://pubs.opengroup.org/onlinepubs/9699919799/basedefs/poll.h.html
 */
#ifndef _POLL_H
#define _POLL_H

/* The <poll.h> header shall define the pollfd structure, which shall
   include at least the following members: */
struct pollfd {
  int    fd;       /* The following descriptor being polled.  */
  short  events;   /* The input event flags (see below).  */
  short  revents;  /* The output event flags (see below).  */
};

/* The <poll.h> header shall define the following type through
   typedef: */

typedef unsigned int nfds_t;
/* An unsigned integer type used for the number of file descriptors. */
/* The implementation shall support one or more programming
   environments in which the width of nfds_t is no greater than the
   width of type long. The names of these programming environments can
   be obtained using the confstr() function or the getconf utility. */

/* The <poll.h> header shall define the following symbolic constants,
   zero or more of which may be OR'ed together to form the events or
   revents members in the pollfd structure: */
#define POLLIN (1<<0) /* Data other than high-priority data may be read without blocking. */
#define POLLRDNORM (1<<1)/* Normal data may be read without blocking. */
#define POLLRDBAND (1<<2)/* Priority data may be read without blocking. */
#define POLLPRI (1<<3)/* High priority data may be read without blocking. */
#define POLLOUT (1<<4)/* Normal data may be written without blocking. */
#define POLLWRNORM (1<<5)/* Equivalent to POLLOUT. */
#define POLLWRBAND (1<<6)/* Priority data may be written. */
#define POLLERR (1<<7)/* An error has occurred ( revents only). */
#define POLLHUP (1<<8)/* Device has been disconnected ( revents only). */
#define POLLNVAL (1<<9)/* Invalid fd member ( revents only). */

/* The significance and semantics of normal, priority, and high-priority data are file and device-specific.  */
/* The following shall be declared as a function and may also be
   defined as a macro. A function prototype shall be provided. */

int   poll(struct pollfd [], nfds_t, int);

#endif
