/* typedef void (*svc_fn_t)(uint32_t uiCommand, */
/*                          tzi_encode_buffer_t *psInBuf,  */
/*                          tzi_encode_buffer_t *psOutBuf, */
/*                          tz_return_t *puiRv); */

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
