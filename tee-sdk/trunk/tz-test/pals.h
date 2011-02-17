#include <stddef.h>
#include <stdint.h>

#include <marshal.h>

typedef enum {
  PAL_WITHOUTPARAM,
  PAL_PARAM,
  PAL_SEAL,
  PAL_UNSEAL,
  PAL_QUOTE
} PAL_CMD;

void pal_entry(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv);
void pal_withoutparam();
uint32_t pal_param(uint32_t input);
tz_return_t pal_seal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen);
tz_return_t pal_unseal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen);
tz_return_t pal_quote(IN uint8_t *nonce, /* assumed to be TPM_NONCE_SIZE */
                      IN uint32_t *tpmsel, /* first element is how many other elements there are */
                      OUT uint8_t *quote, OUT size_t *quote_len);
