#ifndef SCODE_H
#define SCODE_H

#include <stdint.h>
#include <stddef.h>

/* defined for scode sections info */
extern unsigned int __scode_util_start, __scode_util_end;

/* FIXME: copied from paging.h in trustvisor. should use that directly */
#define PAGE_SIZE 0x1000
#define PAGE_SIZE_4K (1UL << 12)
#define PAGE_ALIGN_UP4K(size)   (((size) + PAGE_SIZE_4K - 1) & ~(PAGE_SIZE_4K - 1))
#define PAGE_ALIGN_4K(size)     ((size) & ~(PAGE_SIZE_4K - 1))

enum scode_param_type
  {
    SCODE_PARAM_TYPE_INTEGER = 1,
    SCODE_PARAM_TYPE_POINTER = 2
  };

struct scode_params_struct{
  enum scode_param_type type;
  size_t size; /* in int's */
};

#define SCODE_MAX_PARAMS_NUM 10
struct scode_params_info{
  int params_num;
  struct scode_params_struct pm_str[SCODE_MAX_PARAMS_NUM];
};

enum scode_section_type
  {
    SCODE_SECTION_TYPE_SCODE = 1,
    SCODE_SECTION_TYPE_SDATA = 2,
    SCODE_SECTION_TYPE_PARAM = 3,
    SCODE_SECTION_TYPE_STACK = 4,
    SCODE_SECTION_TYPE_STEXT = 5
  };
struct scode_sections_struct{
  enum scode_section_type type;
  unsigned int start_addr;
  int page_num; /* size of section in pages */
};

#define SCODE_MAX_SECTION_NUM 10  /* max sections that are allowed in scode registration */
struct scode_sections_info{
  int section_num;
  struct scode_sections_struct ps_str[SCODE_MAX_SECTION_NUM];
};

/* read (and optionally write) to the memory pages in the specified
 * range. use this to make sure pages are present for trustvisor
 * (e.g., for pointer parameters before calling a pal function)
 */
int scode_touch_range(void *ptr, size_t len, int do_write);

/* convenience function for getting size of a section from end and start symbols */
size_t scode_ptr_diff(void *end, void *start);

/* initialize an scode_sections_info struct, allocating page-aligned memory
 * for the parameters and stack.
 */
void scode_sections_info_init(struct scode_sections_info *scode_info,
                              void *scode, size_t scode_len,
                              void *sdata, size_t sdata_len,
                              size_t param_sz,
                              size_t stack_sz);

/* add a section to an scode_sections_info struct.
 * The struct should have already been initialized.
 */
void scode_sections_info_add(struct scode_sections_info *scode_info,
                             int type,
                             void *start_addr, size_t len);

/* Print scode_sections_info to stdout */
void scode_sections_info_print(struct scode_sections_info *scode_info);

/* Register a PAL.
 * pageinfo describes the memory areas to be used by the PAL.
 *   FIXME: preconditions? e.g., mandatory vs optional sections?
 * params describes the parameters to the PAL function.
 * entry is a pointer to the PAL function.
 *
 * Once a function is registered, any call to that function
 * will take place in the secure environment.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_register(const struct scode_sections_info *pageinfo,
                   const struct scode_params_info *params,
                   const void *entry);

/* Unregister a PAL.
 * entry is a pointer to a function previously registered
 *   with scode_register
 *
 * After unregistration, calls to the given function
 * no longer take place in the secure environment.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_unregister(void *entry);

/* Test for presence of TrustVisor.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_test(void);

/* Seal data under a pcr value.
 * pcrAtRelease_addr is the required value of pcr #FIXME the
 *   data to be unsealed.
 * in points to the data to be sealed.
 * in_len is the size of the data to be sealed, in bytes
 * out is a pointer at which the sealed data will be stored
 * out_len will be set to the length of the sealed data
 *   FIXME: this is currently output only. TV does not check
 *          that the destination is large enough.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_seal(uint8_t *pcrAtRelease_addr,
               void *in,
               size_t in_len,
               void *out,
               size_t *out_len);

/* unseal data
 * in is a pointer to the data to be unsealed.
 * in_len is the size of the sealed data, in bytes
 * out is a pointer at which the unsealed data will be stored
 * out_len will be set to the length of the unsealed data
 *   FIXME: this is currently output only. TV does not check
 *          that the destination is large enough.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_unseal(void *in,
                 size_t in_len,
                 void *out,
                 size_t *out_len);

/* generate a TPM quote (FIXME of...?)
 * nonce points to a nonce to be used FIXME: size?
 * tpmsel FIXME what is this?
 * out the quote is written here
 * out_len the length of out is written here.
 *   FIXME: output only?
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_quote(uint8_t *nonce,
                uint32_t *tpmsel,
                uint8_t *out,
                size_t *out_len);
#endif
