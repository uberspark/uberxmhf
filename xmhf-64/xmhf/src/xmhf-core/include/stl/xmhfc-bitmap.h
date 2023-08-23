// Bitmap with optimized space and time complexity.  The xmhfstl_bitmap allocates/revoke
// space on demand (PAGE granularity), but adds a little performance overhead
// in the critical path

#ifndef XMHFSTL_BITMAP
#define XMHFSTL_BITMAP

#define BITS_PER_BYTE_SHIFT		3
#define BITS_PER_BYTE			(1 << BITS_PER_BYTE_SHIFT)
#define BITS_TO_BYTES(x)		((x) >> BITS_PER_BYTE_SHIFT)
#define BYTES_TO_BITS(x)		((x) << BITS_PER_BYTE_SHIFT)

#ifndef __ASSEMBLY__

// A xmhfstl_bitmap is allocated in separate memory pages. So we track the use of each
// xmhfstl_bitmap page to allocate/revoke memory on demand
typedef struct{
	uint32_t max_bits;
	char** mem_table; // Contains page aligned addresses for holding xmhfstl_bitmap content
	uint16_t* bits_stat; // num of set bit in the corresponding xmhfstl_bitmap page
}XMHF_STL_BITMAP;

extern XMHF_STL_BITMAP* xmhfstl_bitmap_create(uint32_t num_bits);
extern void xmhfstl_bitmap_destroy(XMHF_STL_BITMAP* bitmap);

extern bool xmhfstl_bitmap_set_bit(XMHF_STL_BITMAP* bitmap, const uint32_t bit_idx);
extern bool xmhfstl_bitmap_clear_bit(XMHF_STL_BITMAP* bitmap, const uint32_t bit_idx);

extern bool xmhfstl_bitmap_is_bit_set(XMHF_STL_BITMAP* bitmap, const uint32_t bit_idx);
extern bool xmhfstl_bitmap_is_bit_clear(XMHF_STL_BITMAP* bitmap, const uint32_t bit_idx);



#endif // __ASSEMBLY__

#endif // XMHFSTL_BITMAP
