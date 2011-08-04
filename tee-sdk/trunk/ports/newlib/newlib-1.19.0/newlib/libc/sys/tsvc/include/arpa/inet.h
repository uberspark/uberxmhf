/* minimal compliance with IEEE Std 1003.1
   http://pubs.opengroup.org/onlinepubs/009695399/basedefs/arpa/inet.h.html#tag_13_03
*/

#ifndef _ARPA_INET_H
#define _ARPA_INET_H

/* The uint32_t and uint16_t types shall be defined as described in
   <inttypes.h>. */
#include <inttypes.h>

/* The in_port_t and in_addr_t types shall be defined as described in
   <netinet/in.h>. */
/* The in_addr structure shall be defined as described in
   <netinet/in.h>. */
/* The INET_ADDRSTRLEN [IP6] and INET6_ADDRSTRLEN macros shall be
   defined as described in <netinet/in.h>. */
#include <netinet/in.h>

/* The following shall either be declared as functions, defined as
   macros, or both. If functions are declared, function prototypes
   shall be provided. */

uint32_t htonl(uint32_t);
uint16_t htons(uint16_t);
uint32_t ntohl(uint32_t);
uint16_t ntohs(uint16_t);

/* The following shall be declared as functions and may also be
   defined as macros. Function prototypes shall be provided. */
in_addr_t    inet_addr(const char *);
char        *inet_ntoa(struct in_addr);
const char  *inet_ntop(int, const void *, char *,
                       socklen_t);
int          inet_pton(int, const char *, void *);

/* Inclusion of the <arpa/inet.h> header may also make visible all
   symbols from <netinet/in.h> and <inttypes.h>. */

#endif
