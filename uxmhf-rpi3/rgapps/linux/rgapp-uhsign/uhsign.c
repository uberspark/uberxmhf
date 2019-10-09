
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>

#include <uhcall.h>
#include <uhsign.h>

__attribute__((aligned(4096))) __attribute__((section(".data"))) uhsign_param_t uhcp;

void do_uhsign(uint8_t *pkt, uint32_t pkt_size) {
  uint32_t i;
  uint8_t *key=(uint8_t *)"super_secret_hmac_key";
  uint32_t key_size = 21;
  uint32_t digest_size=20;
  uhsign_param_t *ptr_uhcp;
  memcpy(ptr_uhcp->pkt, pkt, pkt_size);
  memcpy(ptr_uhcp->key, key, key_size);  
  ptr_uhcp->pkt_size=pkt_size;
  ptr_uhcp->key_size=key_size;
  ptr_uhcp->digest_size=digest_size;

  if(!uhcall(UAPP_UHSIGN_FUNCTION_SIGN, ptr_uhcp, sizeof(uhsign_param_t)))
    printf("hypercall FAILED\n");
  else
    printf("SUCCESS\n");

  for(i=0;i<20;i++)
    printf("%02x", ptr_uhcp->digest[i]);
  printf("\n");
}


int main() {
  uint8_t *data=(uint8_t *)"hello world";
  uint32_t data_len=11;

  do_uhsign(data,data_len);

  return 0;
}
  
