#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "scode.h"
#include "pals.h"
#include "layout.h"
//#include  "config.h"
#include  <sys/mman.h>
#include  <errno.h>
#include  <string.h>

int test_vmcall()
{
  printf("VMMCALL\n");
  scode_test();
  printf("VMMCALL returned\n");
  return 0;
}

int test_withoutparam(struct scode_sections_info *scode_info)
{
  struct scode_params_info null_params_info = 
    {.params_num = 0,
     .pm_str = {}
    };
 
  printf("\nWITHOUTPARAM\n");
  printf("registering PAL\n");
  assert(!scode_register(scode_info, &null_params_info, pal_withoutparam));
  printf("running PAL\n");
  pal_withoutparam();

  printf("unregistering PAL\n");
  scode_unregister(pal_withoutparam);
  return 0;
}

int test_param(struct scode_sections_info *scode_info)
{
  int i;
  uint32_t output;
  int rv=0;
  struct scode_params_info params_info = 
    { 
      .params_num = 2,
      .pm_str =
      {
        {.type = SCODE_PARAM_TYPE_POINTER,  /* pointer */
         .size = sizeof(uint32_t)/sizeof(int)},
        {.type = SCODE_PARAM_TYPE_INTEGER,  /* integer */
         .size = 1}
      }
    };


  printf("\nPARAM\n");
  printf("registering PAL\n");
  assert(!scode_register(scode_info, &params_info, pal_param));

  printf("running PAL\n");
  for(i=0;i<3; i++) { /* FIXME: bump this up when performance issue is addressed */
    pal_param(&output, i);
    if(output != i+1) {
      printf("error: output=%d, i=%d\n", output, i);
      rv=1;
      break;
    }
  }
  printf("unregistering PAL\n");
  scode_unregister(pal_param);

  return rv;
}

int test_seal(struct scode_sections_info *scode_info)
{
  int output = -1;

  struct scode_params_info params_info = 
    { 
      .params_num = 1,
      .pm_str =
      {
        {.type = SCODE_PARAM_TYPE_POINTER,  /* pointer */
         .size = 1}
      }
    };

  printf("\nSEAL\n");
  printf("registering PAL\n");
  assert(!scode_register(scode_info, &params_info, pal_seal));

  printf("running PAL\n");
  pal_seal(&output);
  if (output) {
    printf("error: pal_seal returned %d\n", output);
  }

  printf("unregistering PAL\n");
  scode_unregister(pal_seal);

  return 0;
}

int test_quote(struct scode_sections_info *scode_info)
{
  uint32_t quote[640/sizeof(uint32_t)]; /* FIXME should be TPM_QUOTE_SIZE */
  size_t quote_len=sizeof(quote);

  unsigned char * pdata;
  int num, i,j;

  struct scode_params_info params_info = 
    { 
      .params_num = 2,
      .pm_str =
      {
        {.type = SCODE_PARAM_TYPE_POINTER,
         .size = sizeof(quote)/(sizeof(int))},
        {.type = SCODE_PARAM_TYPE_POINTER,
         .size = sizeof(size_t)/(sizeof(int))}
      }
    };

  printf("\nQUOTE\n");
  printf("registering PAL\n");
  assert(!scode_register(scode_info, &params_info, pal_quote));

  printf("quote[0] before PAL is %d!\n", quote[0]);
  pal_quote((uint8_t*)quote, &quote_len);
  printf("quote[0] after PAL is %d!\n", quote[0]);
  printf("output len = %d!\n", quote_len);

  if (quote[0] != 0x00000101 || quote[1] != 0x544f5551) {
    printf("quote header error!\n");
    return 1;
  }
  num = quote[2];
  if (num > 4) {
    printf("quote pcr sel error!\n");
    return 1;
  }
  pdata = ((uint8_t*)quote)+8+4+4*num;
  for( i=0 ; i<num ; i++ )  {
    printf("PCR[%d] = ", quote[3+i]);
    for (j=0; j<20; j++) 
      printf("%#x ", *(pdata+i*20+j));
    printf("\n");
  }
  pdata = ((uint8_t*)quote)+8+4+24*num;
  printf("nonce = ");
  for( i=0 ; i<20 ; i++ )  
    printf("%x ", *(pdata+i));
  printf("\n");

  printf("unregistering PAL\n");
  scode_unregister(pal_quote);

  return 0;
}

// function main
// register some sensitive code and data in libfoo.so and call bar()
int main(void)
{
  struct scode_sections_info scode_info;
  int rv = 0;

  scode_sections_info_init(&scode_info,
                           &__scode_start, scode_ptr_diff(&__scode_end, &__scode_start),
                           NULL, 0,
                           PAGE_SIZE, PAGE_SIZE);
  printf("scode sections:\n");
  scode_sections_info_print(&scode_info);

#ifdef TEST_VMMCALL
  rv = test_vmcall() || rv;
#endif

#ifdef TEST_WITHOUTPARAM
  rv = test_withoutparam(&scode_info) || rv;
#endif

#ifdef TEST_PARAM
  rv = test_param(&scode_info) || rv;
#endif

#ifdef TEST_SEAL
  rv = test_seal(&scode_info) || rv;
#endif

#ifdef TEST_QUOTE
  rv = test_quote(&scode_info) || rv;
#endif

  if (rv) {
    printf("FAIL with rv=%d\n", rv);
  } else {
    printf("SUCCESS with rv=%d\n", rv);
  }

  return rv;
} 
