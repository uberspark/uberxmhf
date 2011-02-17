#include <stddef.h>
#include <stdint.h>

void pal_withoutparam();
void pal_param(uint32_t *output, int input);
void pal_seal(int *output);
void pal_quote(uint8_t *quote, size_t *quote_len);
