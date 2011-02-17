#ifndef SEALED_CODE_PAL_H
#define SEALED_CODE_PAL_H

/* system */
#include <stdint.h>
#include <stddef.h>

typedef void (*scp_sealed_fn_t)(uint8_t *in, size_t in_len, uint8_t *out, size_t *out_len);

/* #define SCP_MAX_UNSEALED_LEN (10*PAGE_SIZE) */
/* #define SCP_MAX_SEALED_LEN (10*PAGE_SIZE) */
/* #define SCP_MAX_PARAM_LEN (1*PAGE_SIZE) */
/* #define SCP_MAX_OUTPUT_LEN (1*PAGE_SIZE) */
#define SCP_MAX_UNSEALED_LEN (200)
#define SCP_MAX_SEALED_LEN (200)
#define SCP_MAX_PARAM_LEN (200)
#define SCP_MAX_OUTPUT_LEN (200)

size_t scp_sealed_size_of_unsealed_size(size_t in);
void scp_register(void);
void scp_unregister(void);
int scp_seal(uint8_t *incode, size_t incode_len, uint8_t *outcode, size_t *outcode_len);
int scp_run(uint8_t *incode, size_t incode_len,
            uint8_t *params, size_t params_len,
            uint8_t *output, size_t *output_len);


#endif
