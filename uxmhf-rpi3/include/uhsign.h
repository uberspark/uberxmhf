#ifndef __UHSIGN_H__
#define __UHSIGN_H__

#define UAPP_UHSIGN_FUNCTION_SIGN    0x69
#define HMAC_DIGEST_SIZE 20

#ifndef __ASSEMBLY__

typedef struct {
  uint8_t *pkt;
  uint32_t pkt_size;
  uint8_t *digest;
}uhsign_param_t;


#endif // __ASSEMBLY__

#endif // __UHSIGN_H__
