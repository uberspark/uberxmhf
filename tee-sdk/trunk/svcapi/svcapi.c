#include "scode.h"
#include "svcapi.h"

#include <stdint.h>

__attribute__ ((section (".stext")))
int scode_seal(uint8_t *pcrAtRelease_addr,
               void *in,
               size_t in_len,
               void *out,
               size_t *out_len)
{
  int ret;
  unsigned int inbuf1[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf1[2]= {(unsigned int)out, (unsigned int)out_len};

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_SEAL), "c"((unsigned int)inbuf1), "d"(pcrAtRelease_addr), "S"((unsigned int)outbuf1));
  return ret;
}

__attribute__ ((section (".stext")))
int scode_unseal(void *in,
                 size_t in_len,
                 void *out,
                 size_t *out_len)
{
  int ret;
  unsigned int inbuf2[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf2[2]= {(unsigned int)out, (unsigned int)out_len};

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_UNSEAL), "c"((unsigned int)inbuf2), "d"((unsigned int)outbuf2));
  return ret;
}

__attribute__ ((section (".stext")))
int scode_quote(uint8_t *nonce,
                uint32_t *tpmsel,
                uint8_t *out,
                size_t *out_len)
{
  int ret;
  unsigned int outbuf[2]= {(unsigned int)out, (unsigned int)out_len};

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_QUOTE), "S"(nonce), "c"(tpmsel), "d"((unsigned int)outbuf));
  return ret;
}

