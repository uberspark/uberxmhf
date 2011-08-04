/* minimal compliance with IEEE Std 1003.1
   http://pubs.opengroup.org/onlinepubs/009695399/basedefs/sys/socket.h.html
*/

#ifndef _SYS_SOCKET_H
#define _SYS_SOCKET_H

#include <sys/uio.h>

/* The <sys/socket.h> header shall define the type socklen_t, which is
   an integer type of width of at least 32 bits; see APPLICATION
   USAGE. */
typedef unsigned long int socklen_t;

/* The <sys/socket.h> header shall define the unsigned integer type
   sa_family_t. */
#ifndef _SA_FAMILY_T_DECLARED
typedef	unsigned int sa_family_t;
#define	_SA_FAMILY_T_DECLARED
#endif

/* The <sys/socket.h> header shall define the sockaddr structure that
   includes at least the following members: */
struct sockaddr {
  sa_family_t  sa_family;  /* Address family.  */
  char         sa_data[];  /* Socket address (variable-length data).  */
};
/* The sockaddr structure is used to define a socket address which is
   used in the bind(), connect(), getpeername(), getsockname(),
   recvfrom(), and sendto() functions. */

/* The <sys/socket.h> header shall define the sockaddr_storage
   structure. This structure shall be: */
/* Large enough to accommodate all supported protocol-specific address
   structures */
/* Aligned at an appropriate boundary so that pointers to it can be
   cast as pointers to protocol-specific address structures and used
   to access the fields of those structures without alignment
   problems */
/* The sockaddr_storage structure shall contain at least the following
   members: */
struct sockaddr_storage {
  sa_family_t ss_family;
  char data[1]; /* FIXME */
};
/* When a sockaddr_storage structure is cast as a sockaddr structure,
   the ss_family field of the sockaddr_storage structure shall map
   onto the sa_family field of the sockaddr structure. When a
   sockaddr_storage structure is cast as a protocol-specific address
   structure, the ss_family field shall map onto a field of that
   structure that is of type sa_family_t and that identifies the
   protocol's address family. */

/* The <sys/socket.h> header shall define the msghdr structure that
   includes at least the following members: */
struct msghdr {
  void          *msg_name;        /* Optional address.  */
  socklen_t      msg_namelen;     /* Size of address.  */
  struct iovec  *msg_iov;         /* Scatter/gather array.  */
  int            msg_iovlen;      /* Members in msg_iov.  */
  void          *msg_control;     /* Ancillary data; see below.  */
  socklen_t      msg_controllen;  /* Ancillary data buffer len.  */
  int            msg_flags;       /* Flags on received message.  */
};
/* The msghdr structure is used to minimize the number of directly
   supplied parameters to the recvmsg() and sendmsg() functions. This
   structure is used as a value- result parameter in the recvmsg()
   function and value only for the sendmsg() function. */

/* The iovec structure shall be defined as described in <sys/uio.h>
   . */

/* The <sys/socket.h> header shall define the cmsghdr structure that
   includes at least the following members: */
struct cmsghdr {
  socklen_t  cmsg_len;    /* Data byte count, including the cmsghdr.  */
  int        cmsg_level;  /* Originating protocol.  */
  int        cmsg_type;   /* Protocol-specific type.  */
  unsigned char cmsg_data[];
};
/* The cmsghdr structure is used for storage of ancillary data object
   information. */
/* Ancillary data consists of a sequence of pairs, each consisting of
   a cmsghdr structure followed by a data array. The data array
   contains the ancillary data message, and the cmsghdr structure
   contains descriptive information that allows an application to
   correctly parse the data. */
/* The values for cmsg_level shall be legal values for the level
   argument to the getsockopt() and setsockopt() functions. The system
   documentation shall specify the cmsg_type definitions for the
   supported protocols. */
/* Ancillary data is also possible at the socket level. The
   <sys/socket.h> header defines the following macro for use as the
   cmsg_type value when cmsg_level is SOL_SOCKET: */
#define SCM_RIGHTS 1
/* Indicates that the data array contains the access rights to be sent or received. */

/* The <sys/socket.h> header defines the following macros to gain
   access to the data arrays in the ancillary data associated with a
   message header: */
#define CMSG_DATA(cmsg) (cmsg->cmsg_data))

/* If the argument is a pointer to a cmsghdr structure, this macro
   shall return an unsigned character pointer to the data array
   associated with the cmsghdr structure. */
#define CMSG_NXTHDR(mhdr,cmsg) NULL
/* If the first argument is a pointer to a msghdr structure and the
   second argument is a pointer to a cmsghdr structure in the
   ancillary data pointed to by the msg_control field of that msghdr
   structure, this macro shall return a pointer to the next cmsghdr
   structure, or a null pointer if this structure is the last cmsghdr
   in the ancillary data. */

#define CMSG_FIRSTHDR(mhdr) NULL
/* If the argument is a pointer to a msghdr structure, this macro
   shall return a pointer to the first cmsghdr structure in the
   ancillary data associated with this msghdr structure, or a null
   pointer if there is no ancillary data associated with the msghdr
   structure. */

/* The <sys/socket.h> header shall define the linger structure that
   includes at least the following members: */
struct linger {
  int  l_onoff;   /* Indicates whether linger option is enabled.  */
  int  l_linger;  /* Linger time, in seconds.  */
};

/* The <sys/socket.h> header shall define the following macros, with
   distinct integer values: */
#define SOCK_DGRAM 1 /* Datagram socket. */
#define SOCK_RAW 2 /* [RS]  Raw Protocol Interface.  */
#define SOCK_SEQPACKET 3 /* Sequenced-packet socket. */
#define SOCK_STREAM 4 /* Byte-stream socket. */

/* The <sys/socket.h> header shall define the following macro for use
   as the level argument of setsockopt() and getsockopt(). */
#define SOL_SOCKET 1
/* Options to be accessed at socket level, not protocol level. */

/* The <sys/socket.h> header shall define the following macros, with
   distinct integer values, for use as the option_name argument in
   getsockopt() or setsockopt() calls: */
#define SO_ACCEPTCONN 1 /* Socket is accepting connections. */
#define SO_BROADCAST 2 /* Transmission of broadcast messages is supported. */
#define SO_DEBUG 3 /* Debugging information is being recorded. */
#define SO_DONTROUTE 4 /* Bypass normal routing. */
#define SO_ERROR 5 /* Socket error status. */
#define SO_KEEPALIVE 6 /* Connections are kept alive with periodic messages. */
#define SO_LINGER 7 /* Socket lingers on close. */
#define SO_OOBINLINE 8 /* Out-of-band data is transmitted in line. */
#define SO_RCVBUF 9 /* Receive buffer size. */
#define SO_RCVLOWAT 10 /* Receive ``low water mark''. */
#define SO_RCVTIMEO 11 /* Receive timeout. */
#define SO_REUSEADDR 12 /* Reuse of local addresses is supported. */
#define SO_SNDBUF 13 /* Send buffer size. */
#define SO_SNDLOWAT 14 /* Send ``low water mark''. */
#define SO_SNDTIMEO 15 /* Send timeout. */
#define SO_TYPE 16 /* Socket type. */

/* The <sys/socket.h> header shall define the following macro as the
   maximum backlog queue length which may be specified by the backlog
   field of the listen() function: */
#define SOMAXCONN 128 /* The maximum backlog queue length. */

/* The <sys/socket.h> header shall define the following macros, with
   distinct integer values, for use as the valid values for the
   msg_flags field in the msghdr structure, or the flags parameter in
   recvfrom(), recvmsg(), sendmsg(), or sendto() calls: */
#define MSG_CTRUNC 1 /* Control data truncated. */
#define MSG_DONTROUTE 2 /* Send without using routing tables. */
#define MSG_EOR 3 /* Terminates a record (if supported by the
                     protocol). */
#define MSG_OOB 4 /* Out-of-band data. */
#define MSG_PEEK 5 /* Leave received data in queue. */
#define MSG_TRUNC 6 /* Normal data truncated. */
#define MSG_WAITALL 7 /* Attempt to fill the read buffer. */

/* The <sys/socket.h> header shall define the following macros, with
   distinct integer values: */
#define AF_INET 1 /* Internet domain sockets for use with IPv4
                     addresses. */
#define AF_INET6 2 /* [IP6] Internet domain sockets for use with IPv6
                      addresses.  */
#define AF_UNIX 3 /* UNIX domain sockets. */
#define AF_UNSPEC 4 /* Unspecified. */

/* The <sys/socket.h> header shall define the following macros, with
   distinct integer values: */
#define SHUT_RD 1 /* Disables further receive operations. */
#define SHUT_RDWR 2 /* Disables further send and receive operations. */
#define SHUT_WR 3 /* Disables further send operations. */

/* The following shall be declared as functions and may also be
   defined as macros. Function prototypes shall be provided. */
int     accept(int, struct sockaddr *, socklen_t *);
int     bind(int, const struct sockaddr *, socklen_t);
int     connect(int, const struct sockaddr *, socklen_t);
int     getpeername(int, struct sockaddr *, socklen_t *);
int     getsockname(int, struct sockaddr *, socklen_t *);
int     getsockopt(int, int, int, void *, socklen_t *);
int     listen(int, int);
ssize_t recv(int, void *, size_t, int);
ssize_t recvfrom(int, void *, size_t, int,
                 struct sockaddr *, socklen_t *);
ssize_t recvmsg(int, struct msghdr *, int);
ssize_t send(int, const void *, size_t, int);
ssize_t sendmsg(int, const struct msghdr *, int);
ssize_t sendto(int, const void *, size_t, int, const struct sockaddr *,
               socklen_t);
int     setsockopt(int, int, int, const void *, socklen_t);
int     shutdown(int, int);
int     socket(int, int, int);
int     sockatmark(int);
int     socketpair(int, int, int, int[2]);

/* Inclusion of <sys/socket.h> may also make visible all symbols from
   <sys/uio.h>. */

#endif
