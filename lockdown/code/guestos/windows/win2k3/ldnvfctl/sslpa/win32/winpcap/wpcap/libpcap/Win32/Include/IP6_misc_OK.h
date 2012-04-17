/*
 * Copyright (c) 1993, 1994, 1997
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that: (1) source code distributions
 * retain the above copyright notice and this paragraph in its entirety, (2)
 * distributions including binary code include the above copyright notice and
 * this paragraph in its entirety in the documentation or other materials
 * provided with the distribution, and (3) all advertising materials mentioning
 * features or use of this software display the following acknowledgement:
 * ``This product includes software developed by the University of California,
 * Lawrence Berkeley Laboratory and its contributors.'' Neither the name of
 * the University nor the names of its contributors may be used to endorse
 * or promote products derived from this software without specific prior
 * written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 * @(#) $Header: /tcpdump/master/libpcap/win32/include/ip6_misc.h,v 1.0 2000/08/31 13:27:10 mcr Exp $ (LBL)
 */

/*
 * This file contains a collage of declarations for IPv6 from FreeBSD not present in Windows
 */

#ifndef	_NETINET_IN_H
#define	_NETINET_IN_H	1
#endif

#include <winsock2.h>

#ifdef HAVE_ADDRINFO
#include <ws2tcpip.h>
#include <tpipv6.h>
#endif /* HAVE_ADDRINFO */

#define	IN_MULTICAST(a)		IN_CLASSD(a)

#define	IN_EXPERIMENTAL(a)	((((u_int32_t) (a)) & 0xe0000000) == 0xe0000000)

#define	IN_LOOPBACKNET		127

#ifndef HAVE_ADDRINFO
/* IPv6 address */
struct in6_addr
  {
    union
      {
	u_int8_t		u6_addr8[16];
	u_int16_t	u6_addr16[8];
	u_int32_t	u6_addr32[4];
      } in6_u;
#define s6_addr			in6_u.u6_addr8
#define s6_addr16		in6_u.u6_addr16
#define s6_addr32		in6_u.u6_addr32
#define s6_addr64		in6_u.u6_addr64
  };

extern const struct in6_addr in6addr_any;        /* :: */
extern const struct in6_addr in6addr_loopback;   /* ::1 */
#define IN6ADDR_ANY_INIT { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 }
#define IN6ADDR_LOOPBACK_INIT { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1 }
#endif /* HAVE_ADDRINFO */


#define INET_ADDRSTRLEN 16
#define INET6_ADDRSTRLEN 46


#ifndef HAVE_ADDRINFO
typedef unsigned short	sa_family_t;

#define	__SOCKADDR_COMMON(sa_prefix) \
  sa_family_t sa_prefix##family

/* Ditto, for IPv6.  */
struct sockaddr_in6
  {
    __SOCKADDR_COMMON (sin6_);
    u_int16_t sin6_port;		/* Transport layer port # */
    u_int32_t sin6_flowinfo;	/* IPv6 flow information */
    struct in6_addr sin6_addr;	/* IPv6 address */
  };

#define IN6_IS_ADDR_V4MAPPED(a) \
	((((u_int32_t *) (a))[0] == 0) && (((u_int32_t *) (a))[1] == 0) && \
	 (((u_int32_t *) (a))[2] == htonl (0xffff)))

#define IN6_IS_ADDR_MULTICAST(a) (((u_int8_t *) (a))[0] == 0xff)

#define IN6_IS_ADDR_LINKLOCAL(a) \
	((((u_int32_t *) (a))[0] & htonl (0xffc00000)) == htonl (0xfe800000))

#define IN6_IS_ADDR_LOOPBACK(a) \
	(((u_int32_t *) (a))[0] == 0 && ((u_int32_t *) (a))[1] == 0 && \
	 ((u_int32_t *) (a))[2] == 0 && ((u_int32_t *) (a))[3] == htonl (1))
#endif /* HAVE_ADDRINFO */

struct ip6_hdr 
  {
    union 
      {
	struct ip6_hdrctl 
	  {
	    u_int32_t ip6_un1_flow;   /* 24 bits of flow-ID */
	    u_int16_t ip6_un1_plen;   /* payload length */
	    u_int8_t  ip6_un1_nxt;    /* next header */
	    u_int8_t  ip6_un1_hlim;   /* hop limit */
	  } ip6_un1;
	u_int8_t ip6_un2_vfc;       /* 4 bits version, 4 bits priority */
      } ip6_ctlun;
    struct in6_addr ip6_src;      /* source address */
    struct in6_addr ip6_dst;      /* destination address */
  };

/* Fragment header */
struct ip6_frag 
  {
    u_int8_t   ip6f_nxt;       /* next header */
    u_int8_t   ip6f_reserved;  /* reserved field */
    u_int16_t  ip6f_offlg;     /* offset, reserved, and flag */
    u_int32_t  ip6f_ident;     /* identification */
  };

#define ip6_vfc   ip6_ctlun.ip6_un2_vfc
#define ip6_flow  ip6_ctlun.ip6_un1.ip6_un1_flow
#define ip6_plen  ip6_ctlun.ip6_un1.ip6_un1_plen
#define ip6_nxt   ip6_ctlun.ip6_un1.ip6_un1_nxt
#define ip6_hlim  ip6_ctlun.ip6_un1.ip6_un1_hlim
#define ip6_hops  ip6_ctlun.ip6_un1.ip6_un1_hlim

#define IP6F_OFF_MASK       0xf8ff  /* mask out offset from _offlg */
#define IP6F_RESERVED_MASK  0x0600  /* reserved bits in ip6f_offlg */
#define IP6F_MORE_FRAG      0x0100  /* more-fragments flag */
struct nd_opt_hdr             /* Neighbor discovery option header */
  {
    u_int8_t  nd_opt_type;
    u_int8_t  nd_opt_len;        /* in units of 8 octets */
    /* followed by option specific data */
  };

#define  ND_OPT_SOURCE_LINKADDR       1
#define  ND_OPT_TARGET_LINKADDR       2
#define  ND_OPT_PREFIX_INFORMATION    3
#define  ND_OPT_REDIRECTED_HEADER     4
#define  ND_OPT_MTU                   5

struct nd_opt_prefix_info     /* prefix information */
  {
    u_int8_t   nd_opt_pi_type;
    u_int8_t   nd_opt_pi_len;
    u_int8_t   nd_opt_pi_prefix_len;
    u_int8_t   nd_opt_pi_flags_reserved;
    u_int32_t  nd_opt_pi_valid_time;
    u_int32_t  nd_opt_pi_preferred_time;
    u_int32_t  nd_opt_pi_reserved2;
    struct in6_addr  nd_opt_pi_prefix;
  };

#define ND_OPT_PI_FLAG_ONLINK        0x80
#define ND_OPT_PI_FLAG_AUTO          0x40

struct nd_opt_rd_hdr          /* redirected header */
  {
    u_int8_t   nd_opt_rh_type;
    u_int8_t   nd_opt_rh_len;
    u_int16_t  nd_opt_rh_reserved1;
    u_int32_t  nd_opt_rh_reserved2;
    /* followed by IP header and data */
  };

struct nd_opt_mtu             /* MTU option */
  {
    u_int8_t   nd_opt_mtu_type;
    u_int8_t   nd_opt_mtu_len;
    u_int16_t  nd_opt_mtu_reserved;
    u_int32_t  nd_opt_mtu_mtu;
  };

/*
 *	IPV6 extension headers
 */
#define IPPROTO_HOPOPTS		0	/* IPv6 hop-by-hop options	*/
#define IPPROTO_IPV6		41  /* IPv6 header.  */
#define IPPROTO_ROUTING		43	/* IPv6 routing header		*/
#define IPPROTO_FRAGMENT	44	/* IPv6 fragmentation header	*/
#define IPPROTO_ESP		50	/* encapsulating security payload */
#define IPPROTO_AH		51	/* authentication header	*/
#define IPPROTO_ICMPV6		58	/* ICMPv6			*/
#define IPPROTO_NONE		59	/* IPv6 no next header		*/
#define IPPROTO_DSTOPTS		60	/* IPv6 destination options	*/
#define IPPROTO_PIM			103 /* Protocol Independent Multicast.  */

/* Routing header */
struct ip6_rthdr 
  {
    u_int8_t  ip6r_nxt;        /* next header */
    u_int8_t  ip6r_len;        /* length in units of 8 octets */
    u_int8_t  ip6r_type;       /* routing type */
    u_int8_t  ip6r_segleft;    /* segments left */
    /* followed by routing type specific data */
  };

/* Type 0 Routing header */
struct ip6_rthdr0 
  {
    u_int8_t  ip6r0_nxt;       /* next header */
    u_int8_t  ip6r0_len;       /* length in units of 8 octets */
    u_int8_t  ip6r0_type;      /* always zero */
    u_int8_t  ip6r0_segleft;   /* segments left */
    u_int8_t  ip6r0_reserved;  /* reserved field */
    u_int8_t  ip6r0_slmap[3];  /* strict/loose bit map */
    struct in6_addr  ip6r0_addr[1];  /* up to 23 addresses */
  };

#define	 IPV6_RTHDR_TYPE_0 0

#define ICMP6_ROUTER_RENUMBERING	138	/* router renumbering */
#define ICMP6_ROUTER_RENUMBERING_COMMAND  0	/* rr command */
#define ICMP6_ROUTER_RENUMBERING_RESULT   1	/* rr result */

struct mld6_hdr {
         struct  icmp6_hdr       mld6_hdr;
         struct  in6_addr        mld6_addr; /* multicast address */
};

#define mld6_type       mld6_hdr.icmp6_type
#define mld6_code       mld6_hdr.icmp6_code
#define mld6_cksum      mld6_hdr.icmp6_cksum
#define mld6_maxdelay   mld6_hdr.icmp6_data16[0]
#define mld6_reserved   mld6_hdr.icmp6_data16[1]

/* Option types and related macros */
#define IP6OPT_PAD1             0x00    /* 00 0 00000 */
#define IP6OPT_PADN             0x01    /* 00 0 00001 */
#define IP6OPT_JUMBO            0xC2    /* 11 0 00010 = 194 */
#define IP6OPT_JUMBO_LEN        6
#define IP6OPT_RTALERT          0x05    /* 00 0 00101 */
#define IP6OPT_RTALERT_LEN      4
#define IP6OPT_RTALERT_MLD      0       /* Datagram contains an MLD message */
#define IP6OPT_RTALERT_RSVP     1       /* Datagram contains an RSVP message */
#define IP6OPT_RTALERT_ACTNET   2       /* contains an Active Networks msg */
#define IP6OPT_MINLEN           2


#ifndef HAVE_ADDRINFO
#ifndef EAI_ADDRFAMILY
struct addrinfo {
	int	ai_flags;	/* AI_PASSIVE, AI_CANONNAME */
	int	ai_family;	/* PF_xxx */
	int	ai_socktype;	/* SOCK_xxx */
	int	ai_protocol;	/* 0 or IPPROTO_xxx for IPv4 and IPv6 */
	size_t	ai_addrlen;	/* length of ai_addr */
	char	*ai_canonname;	/* canonical name for hostname */
	struct sockaddr *ai_addr;	/* binary address */
	struct addrinfo *ai_next;	/* next structure in linked list */
};
#endif
#endif /* HAVE_ADDRINFO */



/* Hop-by-Hop options header */
/* XXX should we pad it to force alignment on an 8-byte boundary? */
struct ip6_hbh {
        u_int8_t        ip6h_nxt;       /* next header */
        u_int8_t        ip6h_len;       /* length in units of 8 octets */
        /* followed by options */
};

/* Destination options header */
/* XXX should we pad it to force alignment on an 8-byte boundary? */
struct ip6_dest {
        u_int8_t        ip6d_nxt;       /* next header */
        u_int8_t        ip6d_len;       /* length in units of 8 octets */
        /* followed by options */
};

#define IN6_IS_ADDR_UNSPECIFIED(a) \
	(((u_int32_t *) (a))[0] == 0 && ((u_int32_t *) (a))[1] == 0 && \
	 ((u_int32_t *) (a))[2] == 0 && ((u_int32_t *) (a))[3] == 0)	


