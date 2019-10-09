
#include <types>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <uhsign.h>
#include <hmac-sha1.h>

bool uapp_uhsign_handlehcall(u32  uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len)
{
  uhsign_param_t *uhcp;

  if(uhcall_function != UAPP_UHSIGN_FUNCTION_SIGN)
    return false;
  uhcp=(uhsign_param_t *)uhcall_buffer;

  //Call HMAC function
  if(hmac_sha1_memory(uhcp->key, uhcp->key_size, uhcp->pkt, uhcp->pkt_size, uhcp->digest, uhcp->digest_size)==CRYPT_OK)
    return true;

  return false;
}

  
