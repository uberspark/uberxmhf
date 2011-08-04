/* FIXME: From sys/tsvc/sys */
#ifndef _SYS_DIRENT_H
# define _SYS_DIRENT_H

/* linux-compatible place-holder */

#include <sys/types.h>

typedef struct {
} DIR;

/* copied from 'man readdir' */
struct dirent {
  ino_t d_ino;
  off_t d_off;
  unsigned short d_reclen;
  unsigned char d_type;
  char d_name[256];
};

#endif
