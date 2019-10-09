#ifndef __UHSIGN_H__
#define __UHSIGN_H__

#define UAPP_UHSIGN_FUNCTION_SIGN    0x69

#ifndef __Assembly__

typedef struct {
  uint8_t *pkt;
  uint32_t pkt_size;
  uint8_t *key="super_secret_key_for_hmac";
  uint32_t key_size=25;
  uint8_t *digest;
  uint32_t digest_size=20;
}uhsign_param_t;

#endif // __ASSEMBLY__

#endif // __UHSIGN_H__
