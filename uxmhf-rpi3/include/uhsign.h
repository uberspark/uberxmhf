#ifndef __UHSIGN_H__
#define __UHSIGN_H__

#define UAPP_UHSIGN_FUNCTION_SIGN    0x69
#define DIGEST_SIZE 20

#ifndef __Assembly__

typedef struct {
  uint8_t *key;
  uint32_t key_size;
  uint32_t digest_size;
} uhsign_const_params;

struct uhsign_const_params uhsign_consts = { "super_secret_key_for_hmac", 25, 20 };
  
typedef struct {
  uint8_t *pkt;
  uint32_t pkt_size;
  uint8_t *key;
  uint32_t key_size;
  uint8_t *digest;
  uint32_t digest_size;  
}uhsign_param_t;


#endif // __ASSEMBLY__

#endif // __UHSIGN_H__
