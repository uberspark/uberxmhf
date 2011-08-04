/* adapted from IEEE Std 1003.1 spec
   http://pubs.opengroup.org/onlinepubs/009695399/basedefs/netinet/in.h.html
   */

#ifndef _NETINET_IN_H
#define _NETINET_IN_H

#include <inttypes.h>
#include <sys/socket.h>

/* The <netinet/in.h> header shall define the following types: */

typedef uint16_t in_port_t; /* Equivalent to the type uint16_t as
                               defined in <inttypes.h> . */
typedef uint32_t in_addr_t; /* Equivalent to the type uint32_t as
                               defined in <inttypes.h> . */

/* The sa_family_t type shall be defined as described in
   <sys/socket.h>. */

/* The uint8_t and uint32_t type shall be defined as described in
   <inttypes.h>. Inclusion of the <netinet/in.h> header may also make
   visible all symbols from <inttypes.h> and <sys/socket.h>. */

/* The <netinet/in.h> header shall define the in_addr structure that
   includes at least the following member: */
struct in_addr {
  in_addr_t  s_addr;
};

/* The <netinet/in.h> header shall define the sockaddr_in structure
   that includes at least the following members: */
struct sockaddr_in {
  sa_family_t     sin_family;   /* AF_INET.  */
  in_port_t       sin_port;     /* Port number.  */
  struct in_addr  sin_addr;     /* IP address. */
};

/* The sin_port and sin_addr members shall be in network byte
   order. */

/* The sockaddr_in structure is used to store addresses for the
   Internet address family. Values of this type shall be cast by
   applications to struct sockaddr for use with socket functions. */

/* [IP6] The <netinet/in.h> header shall define the in6_addr structure
   that contains at least the following member: */
struct in6_addr {
  uint8_t s6_addr[16];
};
/* This array is used to contain a 128-bit IPv6 address, stored in
   network byte order. */

/* The <netinet/in.h> header shall define the sockaddr_in6 structure
   that includes at least the following members: */
struct sockaddr_in6 {
  sa_family_t      sin6_family;    /* AF_INET6.  */
  in_port_t        sin6_port;      /* Port number.  */
  uint32_t         sin6_flowinfo;  /* IPv6 traffic class and flow information.  */
  struct in6_addr  sin6_addr;      /* IPv6 address.  */
  uint32_t         sin6_scope_id;  /* Set of interfaces for a scope.  */
};
/* The sin6_port and sin6_addr members shall be in network byte order. */

  /* The sockaddr_in6 structure shall be set to zero by an application
     prior to using it, since implementations are free to have
     additional, implementation-defined fields in sockaddr_in6. */

  /* The sin6_scope_id field is a 32-bit integer that identifies a set
     of interfaces as appropriate for the scope of the address carried
     in the sin6_addr field. For a link scope sin6_addr, the
     application shall ensure that sin6_scope_id is a link index. For
     a site scope sin6_addr, the application shall ensure that
     sin6_scope_id is a site index. The mapping of sin6_scope_id to an
     interface or set of interfaces is implementation-defined. */

/* The <netinet/in.h> header shall declare the following external
   variable: */
const struct in6_addr in6addr_any;
/* This variable is initialized by the system to contain the wildcard
   IPv6 address. The <netinet/in.h> header also defines the
   IN6ADDR_ANY_INIT macro. This macro must be constant at compile time
   and can be used to initialize a variable of type struct in6_addr to
   the IPv6 wildcard address. */

/* The <netinet/in.h> header shall declare the following external
   variable: */
const struct in6_addr in6addr_loopback;
/* This variable is initialized by the system to contain the loopback
   IPv6 address. The <netinet/in.h> header also defines the
   IN6ADDR_LOOPBACK_INIT macro. This macro must be constant at compile
   time and can be used to initialize a variable of type struct
   in6_addr to the IPv6 loopback address. */

/* The <netinet/in.h> header shall define the ipv6_mreq structure that
   includes at least the following members: */
struct ipv6_mreq {
  struct in6_addr  ipv6mr_multiaddr;  /* IPv6 multicast address.  */
  unsigned         ipv6mr_interface;  /* Interface index.  */
};

/* The <netinet/in.h> header shall define the following macros for use
   as values of the level argument of getsockopt() and
   setsockopt(): */

#define IPPROTO_IP 1 /* Internet protocol. */
#define IPPROTO_IPV6 2 /* [IP6]  Internet Protocol Version 6.  */
#define IPPROTO_ICMP 3 /* Control message protocol. */
#define IPPROTO_RAW 4 /* [RS]  Raw IP Packets Protocol.  */
#define IPPROTO_TCP 5 /* Transmission control protocol. */
#define IPPROTO_UDP 6 /* User datagram protocol. */

/* The <netinet/in.h> header shall define the following macros for use
   as destination addresses for connect(), sendmsg(), and sendto(): */
#define INADDR_ANY 1 /* IPv4 local host address. */
#define INADDR_BROADCAST 2 /* IPv4 broadcast address. */

/* The <netinet/in.h> header shall define the following macro to help
   applications declare buffers of the proper size to store IPv4
   addresses in string form: */
#define INET_ADDRSTRLEN 16 /* Length of the string form for IP. */

/* The htonl(), htons(), ntohl(), and ntohs() functions shall be
   available as defined in <arpa/inet.h>. Inclusion of the
   <netinet/in.h> header may also make visible all symbols from
   <arpa/inet.h>. */
#include <arpa/inet.h>

/* IP6] The <netinet/in.h> header shall define the following macro to
   help applications declare buffers of the proper size to store IPv6
   addresses in string form: */
#define INET6_ADDRSTRLEN 46 /* Length of the string form for IPv6. */

/* The <netinet/in.h> header shall define the following macros, with
   distinct integer values, for use in the option_name argument in the
   getsockopt() or setsockopt() functions at protocol level
   IPPROTO_IPV6: */
#define IPV6_JOIN_GROUP 1 /* Join a multicast group. */
#define IPV6_LEAVE_GROUP 2 /* Quit a multicast group. */
#define IPV6_MULTICAST_HOPS 3 /* Multicast hop limit. */
#define IPV6_MULTICAST_IF 4 /* Interface to use for outgoing multicast packets. */
#define IPV6_MULTICAST_LOOP 5 /* Multicast packets are delivered back to the local application. */
#define IPV6_UNICAST_HOPS 6 /* Unicast hop limit. */
#define IPV6_V6ONLY 7 /* Restrict AF_INET6 socket to IPv6 communications only. */

/* The <netinet/in.h> header shall define the following macros that
   test for special IPv6 addresses. Each macro is of type int and
   takes a single argument of type const struct in6_addr *: */
#define IN6_IS_ADDR_UNSPECIFIED(x) 0 /* Unspecified address. */
#define IN6_IS_ADDR_LOOPBACK(x) 0 /* Loopback address. */
#define IN6_IS_ADDR_MULTICAST(x) 0 /* Multicast address. */
#define IN6_IS_ADDR_LINKLOCAL(x) 0 /* Unicast link-local address. */
#define IN6_IS_ADDR_SITELOCAL(x) 0 /* Unicast site-local address. */
#define IN6_IS_ADDR_V4MAPPED(x) 0 /* IPv4 mapped address. */
#define IN6_IS_ADDR_V4COMPAT(x) 0/* IPv4-compatible address. */
#define IN6_IS_ADDR_MC_NODELOCAL(x) 0 /* Multicast node-local address. */
#define IN6_IS_ADDR_MC_LINKLOCAL(x) 0 /* Multicast link-local address. */
#define IN6_IS_ADDR_MC_SITELOCAL(x) 0 /* Multicast site-local address. */
#define IN6_IS_ADDR_MC_ORGLOCAL(x) 0 /* Multicast organization-local address. */
#define IN6_IS_ADDR_MC_GLOBAL(x) 0 /* Multicast global address.  */

#endif
