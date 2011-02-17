#include <trustzone.h>

void
TZIEncodeUint32(INOUT tzi_encode_buffer_t* psBuffer,
                uint32_t uiData);
uint32_t
TZIDecodeUint32(INOUT tzi_encode_buffer_t* psBuffer);

void
TZIEncodeArray(INOUT tzi_encode_buffer_t* psBuffer,
               IN void const * pkArray,
               uint32_t uiLength);
void*
TZIEncodeArraySpace(INOUT tzi_encode_buffer_t* psBuffer,
                    uint32_t uiLength);
void *
TZIDecodeArraySpace(INOUT tzi_encode_buffer_t* psBuffer,
                    OUT uint32_t* puiLength);

void
TZIEncodeToDecode(INOUT tzi_encode_buffer_t* psBuffer);

void
TZIEncodeBufInit(INOUT tzi_encode_buffer_t* psBuffer, uint32_t uiLength);

void
TZIEncodeBufReInit(INOUT tzi_encode_buffer_t* psBuffer);

tz_return_t
TZIDecodeGetError(INOUT tzi_encode_buffer_t* psBuffer);
