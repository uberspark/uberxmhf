#include <stdint.h>
#include  "pals.h"
#include  "scode.h"

/* sensitive code  */
__attribute__ ((section (".scode")))
void pal_withoutparam(void) 
{
  asm("nop"::);
  asm("nop"::);
  asm("nop"::);
  asm("nop"::);
}

__attribute__ ((section (".scode")))
void pal_param(uint32_t *output, int input) 
{
  *output = input + 1;
}

__attribute__ ((section (".scode")))
void pal_seal(int *output)
{
  int i;
  uint8_t inputdata[16]="I am input data!";
  size_t inputlen = 16;
  uint8_t outputdata[100]="";
  size_t outputlen;
  uint8_t tmp [100]="";
  unsigned int tmplen;

  scode_seal(NULL, inputdata, inputlen, outputdata, &outputlen);

  scode_unseal(outputdata, outputlen, tmp, &tmplen);

  if (tmplen != inputlen) {
    *output = 1;
    return;
  }

  for( i=0 ; i<tmplen ; i++ )  {
    if (tmp[i]!=inputdata[i]) {
      *output = 2;
      return;
    }
  }
  *output = 0;
}

__attribute__ ((section (".scode")))
void pal_quote(uint8_t *quote, size_t *quote_len) 
{
  int i;
  uint8_t nonce[20];
  uint8_t tpmsel[8];
  *((unsigned int *)tpmsel)=1;
  *((unsigned int *)(tpmsel+4))=0;

  for( i=0 ; i<20 ; i++ )  {
    nonce[i]=((char)i)+tpmsel[i%8];
  }

  scode_quote(nonce, tpmsel, quote, quote_len);
}
