#include <lockdown/types.h>
#include <lockdown/lockdown.h>
#include <lockdown/string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <r_common.h>
#include <r_time.h>

char xinet_ntoa_buf[sizeof "aaa.bbb.ccc.ddd"];

char *inet_ntoa(struct in_addr ina)
{
        unsigned char *ucp = (unsigned char *)&ina;

        snprintf(xinet_ntoa_buf, sizeof(xinet_ntoa_buf), "%d.%d.%d.%d",
                 ucp[0] & 0xff,
                 ucp[1] & 0xff,
                 ucp[2] & 0xff,
                 ucp[3] & 0xff);
        return xinet_ntoa_buf;
}



uint32_t ntohl(x)
	uint32_t x;
{
	u_char *s = (u_char *)&x;
	return (uint32_t)(s[0] << 24 | s[1] << 16 | s[2] << 8 | s[3]);
}

uint16_t
ntohs(x)
	uint16_t x;
{
	u_char *s = (u_char *) &x;
	return (uint16_t)(s[0] << 8 | s[1]);
}

struct hostent *gethostbyaddr(const void *addr, socklen_t len,
       int type){
	return (struct hostent *)0;
}

int gettimeofday(struct timeval *tp, void *tzp){
	tp->tv_sec=0;
	tp->tv_usec=0;
}

char* strtok(char *s, const char *delim)
{
  const char *spanp;
  int c, sc;
  char *tok;
  static char *last;
   
  if (s == NULL && (s = last) == NULL)
    return (NULL);

  /*
   * Skip (span) leading delimiters (s += strspn(s, delim), sort of).
   */
 cont:
  c = *s++;
  for (spanp = delim; (sc = *spanp++) != 0;) {
    if (c == sc)
      goto cont;
  }

  if (c == 0) {			/* no non-delimiter characters */
    last = NULL;
    return (NULL);
  }
  tok = s - 1;

  /*
   * Scan token (scan for delimiters: s += strcspn(s, delim), sort of).
   * Note that delim must have one NUL; we stop if we see that, too.
   */
  for (;;) {
    c = *s++;
    spanp = delim;
    do {
      if ((sc = *spanp++) == c) {
	if (c == 0)
	  s = NULL;
	else
	  s[-1] = 0;
	last = s;
	return (tok);
      }
    } while (sc != 0);
  }
  /* NOTREACHED */
}

