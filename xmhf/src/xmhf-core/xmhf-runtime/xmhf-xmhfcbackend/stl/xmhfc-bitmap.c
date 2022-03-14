#include <xmhf.h>

XMHF_STL_BITMAP* xmhfstl_bitmap_create(uint32_t num_bits)
{
	XMHF_STL_BITMAP* result = NULL;
	uint32_t num_pages = 0;

	result = (XMHF_STL_BITMAP*)xmhf_mm_malloc(sizeof(XMHF_STL_BITMAP));
	if(!result)
		return NULL;

	num_pages = BYTES_TO_PAGE4K(BITS_TO_BYTES(num_bits));
	result->max_bits = num_bits;
	result->mem_table = (char**)xmhf_mm_malloc(num_pages * sizeof(char*));
	if(!result->mem_table)
		return NULL;

	result->bits_stat = (uint16_t*)xmhf_mm_malloc(num_pages * sizeof(uint16_t));
	if(!result->bits_stat)
		return NULL;
	return result;
}

void xmhfstl_bitmap_destroy(XMHF_STL_BITMAP* bitmap)
{
	uint32_t num_pages;
	uint32_t i = 0;

	if(!bitmap)
		return;

	num_pages = BYTES_TO_PAGE4K(BITS_TO_BYTES(bitmap->max_bits));
	for(i = 0; i < num_pages; i++)
	{
		char* mem = bitmap->mem_table[i];

		if(mem)
		{
			xmhf_mm_free(mem);
			mem = NULL;
		}
	}

	if(bitmap->mem_table)
	{
		xmhf_mm_free(bitmap->mem_table);
		bitmap->mem_table = NULL;
	}

	if(bitmap->bits_stat)
	{
		xmhf_mm_free(bitmap->bits_stat);
		bitmap->mem_table = NULL;
	}

	xmhf_mm_free(bitmap);
}

bool xmhfstl_bitmap_set_bit(XMHF_STL_BITMAP* bitmap, const uint32_t bit_idx)
{
	uint32_t bit_offset;
	uint32_t byte_offset;
	uint32_t pg_offset;
	uint32_t bits_stat;
	char test_bit;

	// Sanity check
	if(!bitmap)
		return false;

	if(bit_idx >= bitmap->max_bits)
		return false;

	bit_offset = bit_idx % BITS_PER_BYTE;
	byte_offset = BITS_TO_BYTES(bit_idx) % PAGE_SIZE_4K;
	pg_offset = BITS_TO_BYTES(bit_idx) >> PAGE_SHIFT_4K;

	bits_stat = bitmap->bits_stat[pg_offset];

	if(!bits_stat)
	{
		// There is no page to hold the bitmap content
		bitmap->mem_table[pg_offset] = (char*) xmhf_mm_malloc_align(PAGE_SIZE_4K, PAGE_SIZE_4K);
		if(!bitmap->mem_table[pg_offset])
			return false;
	}

	test_bit = bitmap->mem_table[pg_offset][byte_offset];
	if(test_bit & (1 << bit_offset))
		return true;  // already set
	else
		bitmap->mem_table[pg_offset][byte_offset] = (char)(test_bit | (1 << bit_offset));
	bitmap->bits_stat[pg_offset] = bits_stat + 1;

	return true;
}


bool xmhfstl_bitmap_clear_bit(XMHF_STL_BITMAP* bitmap, const uint32_t bit_idx)
{
	uint32_t bit_offset;
	uint32_t byte_offset;
	uint32_t pg_offset;
	uint32_t bits_stat;
	char test_bit;

	// Sanity check
	if(!bitmap)
		return false;

	if(bit_idx >= bitmap->max_bits)
		return false;

	bit_offset = bit_idx % BITS_PER_BYTE;
	byte_offset = BITS_TO_BYTES(bit_idx) % PAGE_SIZE_4K;
	pg_offset = BITS_TO_BYTES(bit_idx) >> PAGE_SHIFT_4K;
	bits_stat = bitmap->bits_stat[pg_offset];

	if(!bits_stat)
		return true;

	test_bit = bitmap->mem_table[pg_offset][byte_offset];
	if(test_bit & (1 << bit_offset))
	{
		// The bit is set, so we need to clear it in the next
		bitmap->mem_table[pg_offset][byte_offset] = (char)(test_bit & ~(1 << bit_offset));
		bitmap->bits_stat[pg_offset] = bits_stat - 1;
	}

	if(!bits_stat && bitmap->mem_table[pg_offset])
	{
		// There is no page to hold the xmhfstl_bitmap content
		xmhf_mm_free(bitmap->mem_table[pg_offset]);
		bitmap->mem_table[pg_offset] = NULL;
	}

	return true;
}

bool xmhfstl_bitmap_is_bit_set(XMHF_STL_BITMAP* bitmap, const uint32_t bit_idx)
{
	uint32_t bit_offset;
	uint32_t byte_offset;
	uint32_t pg_offset;

	bit_offset = bit_idx % BITS_PER_BYTE;
	byte_offset = BITS_TO_BYTES(bit_idx) % PAGE_SIZE_4K;
	pg_offset = BITS_TO_BYTES(bit_idx) >> PAGE_SHIFT_4K;

	if( !bitmap->mem_table[pg_offset])
		return false;

	if(bitmap->mem_table[pg_offset][byte_offset] & (1 << bit_offset))
		return true;
	else
		return false;
}

bool xmhfstl_bitmap_is_bit_clear(XMHF_STL_BITMAP* bitmap, const uint32_t bit_idx)
{
	uint32_t bit_offset;
	uint32_t byte_offset;
	uint32_t pg_offset;

	bit_offset = bit_idx % BITS_PER_BYTE;
	byte_offset = BITS_TO_BYTES(bit_idx) % PAGE_SIZE_4K;
	pg_offset = BITS_TO_BYTES(bit_idx) >> PAGE_SHIFT_4K;

	if(!bitmap->mem_table[pg_offset])
		return true;

	if(bitmap->mem_table[pg_offset][byte_offset] & (1 << bit_offset))
		return false;
	else
		return true;
}
