#ifndef TZDEV_TRUSTVISOR_H
#define TZDEV_TRUSTVISOR_H

#include <tz.h>

typedef void (*pal_fn_t)(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv);

typedef struct {
  struct scode_sections_info *sPageInfo;
  struct scode_params_info *sParams;
  pal_fn_t pEntry;
} tv_service_t;

#endif
