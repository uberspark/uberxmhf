#include <stdint.h>
#include <stdlib.h>

/* increment each byte */
void f(uint8_t *in, size_t in_len, uint8_t *out, size_t *out_len)
{
  int i;
  if (*out_len < in_len) {
    *out_len = 0;
    return;
  }

  for(i = 0; i < (in_len-1); i++) {
    if (in[i] == '\0') {
      break;
    } else {
      out[i] = in[i]+1;
    }
  }
  out[i++] = '\0';

  *out_len = i;
}
