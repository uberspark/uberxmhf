/* adapted from IEEE Std 1003.1
   http://pubs.opengroup.org/onlinepubs/009695399/basedefs/netdb.h.html
   */

#ifndef _NETDB_H
#define _NETDB_H

#include <inttypes.h>
#include <netinet/in.h>

/* The <netdb.h> header may make available the type in_port_t and the
   type in_addr_t as defined in the description of <netinet/in.h>. */

/* The <netdb.h> header defines the hostent structure that includes at
   least the following members: */
struct hostent {
  char  *h_name;      /* Official name of the host. */
  char **h_aliases;   /* A pointer to an array of pointers to
                         alternative host names, terminated by a null
                         pointer. */
  int    h_addrtype;  /* Address type. */
  int    h_length;    /* The length, in bytes, of the address. */
  char **h_addr_list; /* A pointer to an array of pointers to network
                         addresses (in network byte order) for the
                         host, terminated by a null pointer. */
};

/* The <netdb.h> header defines the netent structure that includes at
   least the following members: */

struct netent {
  char  *n_name;      /* Official, fully-qualified (including the domain) name of the host. */
  char **n_aliases;   /* A pointer to an array of pointers to
                         alternative network names, terminated by a
                         null pointer. */
  int    n_addrtype;  /* The address type of the network. */
  uint32_t n_net;     /* The network number, in host byte order. */
};
/* The uint_32_t type is made available by inclusion of <inttypes.h> (see referenced document XSH). */

/* The <netdb.h> header defines the protoent structure that includes
   at least the following members: */
struct protoent {
  char  *p_name;      /* Official name of the protocol. */
  char **p_aliases;   /* A pointer to an array of pointers to
                         alternative protocol names, terminated by a
                         null pointer. */
  int    p_proto;     /* The protocol number. */
};

/* The <netdb.h> header defines the servent structure that includes at
   least the following members: */
struct servent {
  char  *s_name;      /* Official name of the service. */
  char **s_aliases;   /* A pointer to an array of pointers to
                         alternative service names, terminated by a
                         null pointer. */
  int    s_port;      /* The port number at which the service resides,
                         in network byte order. */
  char  *s_proto;     /* The name of the protocol to use when
                         contacting the service. */
};

/* The <netdb.h> header defines the macro IPPORT_RESERVED with the
   value of the highest reserved Internet port number. */
#define IPPORT_RESERVED 1024

/* The <netdb.h> header provides a declaration of h_errno as a
   modifiable l-value of type int. For example: */
extern int h_errno;

/* The <netdb.h> header defines the following macros for use as error
   values for gethostbyaddr() and gethostbyname(): */
#define HOST_NOT_FOUND 0
#define NO_DATA        1
#define NO_RECOVERY    2
#define TRY_AGAIN      3

/* The <netdb.h> header shall define the addrinfo structure that
   includes at least the following members: */
struct addrinfo {
  int               ai_flags;      /* Input flags.  */
  int               ai_family;     /* Address family of socket.  */
  int               ai_socktype;   /* Socket type.  */
  int               ai_protocol;   /* Protocol of socket.  */
  socklen_t         ai_addrlen;    /* Length of socket address.  */
  struct sockaddr  *ai_addr;       /* Socket address of socket.  */
  char             *ai_canonname;  /* Canonical name of service location.  */
  struct addrinfo  *ai_next;       /* Pointer to next in list.  */
};

/* The <netdb.h> header shall define the following macros that
   evaluate to bitwise-distinct integer constants for use in the flags
   field of the addrinfo structure: */
#define AI_PASSIVE (1<<0) /* Socket address is intended for bind(). */
#define AI_CANONNAME (1<<1) /* Request for canonical name. */
#define AI_NUMERICHOST (1<<2) /* Return numeric host address as
                                 name. */
#define AI_NUMERICSERV (1<<3) /* Inhibit service name resolution. */
#define AI_V4MAPPED (1<<4) /* If no IPv6 addresses are found, query
                              for IPv4 addresses and return them to
                              the caller as IPv4-mapped IPv6
                              addresses. */
#define AI_ALL (1<<5) /* Query for both IPv4 and IPv6 addresses. */
#define AI_ADDRCONFIG (1<<6) /* Query for IPv4 addresses only when an
                                IPv4 address is configured; query for
                                IPv6 addresses only when an IPv6
                                address is configured. */

/* The <netdb.h> header shall define the following macros that
   evaluate to bitwise-distinct integer constants for use in the flags
   argument to getnameinfo(): */
#define NI_NOFQDN (1<<0) /* Only the nodename portion of the FQDN is returned for local hosts. */
#define NI_NUMERICHOST (1<<1) /* The numeric form of the node's address is returned instead of its name. */
#define NI_NAMEREQD (1<<2) /* Return an error if the node's name cannot be located in the database. */
#define NI_NUMERICSERV (1<<3) /* The numeric form of the service address is returned instead of its name. */
#define NI_NUMERICSCOPE (1<<4) /* For IPv6 addresses, the numeric form of the scope identifier is returned instead of its name. */
#define NI_DGRAM (1<<5) /* Indicates that the service is a datagram service (SOCK_DGRAM). */

/* The <netdb.h> header shall define the following macros for use as
   error values for getaddrinfo() and getnameinfo(): */

#define EAI_AGAIN 1 /* The name could not be resolved at this
                     time. Future attempts may succeed. */
#define EAI_BADFLAGS 2 /* The flags had an invalid value. */
#define EAI_FAIL 3 /* A non-recoverable error occurred. */
#define EAI_FAMILY 4 /* The address family was not recognized or the
                      address length was invalid for the specified
                      family. */
#define EAI_MEMORY 5 /* There was a memory allocation failure. */
#define EAI_NONAME 6 /* The name does not resolve for the supplied
                      parameters. */
#define EAI_SERVICE 7 /* The service passed was not recognized for the
                         specified socket type. */
#define EAI_SOCKTYPE 8 /* The intended socket type was not
                          recognized. */
#define EAI_SYSTEM 9 /* A system error occurred. The error code can
                         be found in errno. */
#define EAI_OVERFLOW 10 /* An argument buffer overflowed. */

/* The following are declared as functions, and may also be defined as
   macros: */
void             endhostent(void);
void             endnetent(void);
void             endprotoent(void);
void             endservent(void);
struct hostent  *gethostbyaddr(const void *addr, size_t len, int type);
struct hostent  *gethostbyname(const char *name);
struct hostent  *gethostent(void);
struct netent   *getnetbyaddr(uint32_t net, int type);
struct netent   *getnetbyname(const char *name);
struct netent   *getnetent(void);
struct protoent *getprotobyname(const char *name);
struct protoent *getprotobynumber(int proto);
struct protoent *getprotoent(void);
struct servent  *getservbyname(const char *name, const char *proto);
struct servent  *getservbyport(int port, const char *proto);
struct servent  *getservent(void);
void             sethostent(int stayopen);
void             setnetent(int stayopen);
void             setprotoent(int stayopen);
void             setservent(int stayopen);

/* Inclusion of the <netdb.h> header may also make visible all symbols from <netinet/in.h> and <inttypes.h>. */

/**** Not part of IEEE Std 1003.1 standard, but present in bsd
      implementation and depended upon by some clients ****/

/*
 * Constants for getnameinfo()
 */
#define	NI_MAXHOST	1025
#define	NI_MAXSERV	32

#endif
