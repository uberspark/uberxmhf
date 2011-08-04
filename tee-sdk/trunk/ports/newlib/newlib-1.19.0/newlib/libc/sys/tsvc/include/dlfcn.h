#ifndef _DLFCN_H
#define _DLFCN_H

#define RTLD_LAZY     0
#define RTLD_NOW      1
#define RTLD_GLOBAL   2
#define RTLD_LOCAL    3
#define RTLD_NODELETE 4
#define RTLD_NOLOAD   5
#define RTLD_DEEPBIND 6

void *dlopen(const char* filename, int flag);

char *dlerror(void);

void *dlsym(void *handle, const char *symbol);

int dlclose(void *handle);


#ifdef _GNU_SOURCE
#define RTLD_DEFAULT NULL
#define RTLD_NEXT NULL

typedef struct {
  const char *dli_fname;  /* Pathname of shared object that
                             contains address */
  void       *dli_fbase;  /* Address at which shared object
                             is loaded */
  const char *dli_sname;  /* Name of nearest symbol with address
                             lower than addr */
  void       *dli_saddr;  /* Exact address of symbol named
                             in dli_sname */
} Dl_info;

int dladdr(void *addr, Dl_info *info);
void *dlvsym(void *handle, char *symbol, char *version);
#endif


#endif
