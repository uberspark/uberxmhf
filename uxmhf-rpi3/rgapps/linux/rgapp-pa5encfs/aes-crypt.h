/* aes-crypt.h
 * High level function interface for performing AES encryption on FILE pointers
 * Uses OpenSSL libcrypto EVP API
 *
 * By Andy Sayler (www.andysayler.com)
 * Created  04/17/12
 * Modified 04/18/12
 *
 * Derived from OpenSSL.org EVP_Encrypt_* Manpage Examples
 * http://www.openssl.org/docs/crypto/EVP_EncryptInit.html#EXAMPLES
 *
 * With additional information from Saju Pillai's OpenSSL AES Example
 * http://saju.net.in/blog/?p=36
 * http://saju.net.in/code/misc/openssl_aes.c.txt
 *
 */

#ifndef AES_CRYPT_H
#define AES_CRYPT_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/evp.h>
#include <openssl/aes.h>

#define BLOCKSIZE 1024
#define FAILURE 0
#define SUCCESS 1

/* int do_crypt(FILE* in, FILE* out, int action, char* key_str)
 * Purpose: Perform cipher on in File* and place result in out File*
 * Args: FILE* in      : Input File Pointer
 *       FILE* out     : Output File Pointer
 *       int action    : Cipher action (1=encrypt, 0=decrypt, -1=pass-through (copy))
 *	 char* key_str : C-string containing passpharse from which key is derived
 * Return: FAILURE on error, SUCCESS on success
 */
extern int do_crypt(FILE* in, FILE* out, int action, char* key_str);

#endif
