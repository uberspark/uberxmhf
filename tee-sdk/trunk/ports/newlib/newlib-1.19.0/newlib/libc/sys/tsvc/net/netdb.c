#include <netdb.h>

void             endhostent(void)
{}

void             endnetent(void)
{}

void             endprotoent(void)
{}

void             endservent(void)
{}

struct hostent  *gethostbyaddr(const void *addr, size_t len, int type)
{ return NULL; }

struct hostent  *gethostbyname(const char *name)
{ return NULL; }

struct hostent  *gethostent(void)
{ return NULL; }

struct netent   *getnetbyaddr(uint32_t net, int type)
{ return NULL; }

struct netent   *getnetbyname(const char *name)
{ return NULL; }

struct netent   *getnetent(void)
{ return NULL; }

struct protoent *getprotobyname(const char *name)
{ return NULL; }

struct protoent *getprotobynumber(int proto)
{ return NULL; }

struct protoent *getprotoent(void)
{ return NULL; }

struct servent  *getservbyname(const char *name, const char *proto)
{ return NULL; }

struct servent  *getservbyport(int port, const char *proto)
{ return NULL; }

struct servent  *getservent(void)
{ return NULL; }

void             sethostent(int stayopen)
{}
void             setnetent(int stayopen)
{}
void             setprotoent(int stayopen)
{}
void             setservent(int stayopen)
{}
