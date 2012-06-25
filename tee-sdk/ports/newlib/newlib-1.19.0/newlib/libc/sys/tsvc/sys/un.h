/* based on IEEE Std 1003.1-2008
 * http://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_un.h.html
 */

/* The <sys/un.h> header shall define the sockaddr_un structure, which
   shall include at least the following members: */
struct sockaddr_un {
  sa_family_t  sun_family;  /* Address family.  */
  char         sun_path[100];  /* Socket pathname.  */
};
/* The sockaddr_un structure is used to store addresses for UNIX
   domain sockets. Values of this type shall be cast by applications
   to struct sockaddr for use with socket functions. */

/* The <sys/un.h> header shall define the sa_family_t type as
   described in <sys/socket.h>. */
#ifndef _SA_FAMILY_T_DECLARED
typedef	__sa_family_t	sa_family_t;
#define	_SA_FAMILY_T_DECLARED
#endif

