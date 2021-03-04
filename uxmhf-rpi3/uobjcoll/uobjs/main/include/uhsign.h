#ifndef __UHSIGN_H__
#define __UHSIGN_H__

#include <uberspark/uobjrtl/crt/include/stdint.h>
//#include <inttypes.h>
//#include <uberspark/include/uberspark.h>

#define UAPP_UHSIGN_FUNCTION_SIGN    0x69
#define HMAC_DIGEST_SIZE 32

#ifndef __ASSEMBLY__

typedef struct {
  uint8_t pkt[1600];
  uint32_t pkt_size;
  uint8_t digest[HMAC_DIGEST_SIZE];
  uint32_t vaddr;
}uhsign_param_t;


#endif // __ASSEMBLY__

#endif // __UHSIGN_H__
