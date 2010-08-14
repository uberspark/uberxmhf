/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

/* a stripped down version of x509parse.c from PolarSSL
 * only contains code for parsing DER format RSA private key*/
#include  "parse.h"
//#include  "puttymem.h"
#include  "rsa.h"
//#include  "ssl_private.h"
#include  <stdio.h>
#include  <stdlib.h>
#include  <string.h>

/*
 * Decode a base64-formatted buffer
 */
int base64_decode( unsigned char *dst, int *dlen,
                   unsigned char *src, int  slen )
{
    int i, j, n;
    unsigned long x;
    unsigned char *p;
    unsigned char base64_dec_map[128] =
	{
    127, 127, 127, 127, 127, 127, 127, 127, 127, 127,
    127, 127, 127, 127, 127, 127, 127, 127, 127, 127,
    127, 127, 127, 127, 127, 127, 127, 127, 127, 127,
    127, 127, 127, 127, 127, 127, 127, 127, 127, 127,
    127, 127, 127,  62, 127, 127, 127,  63,  52,  53,
     54,  55,  56,  57,  58,  59,  60,  61, 127, 127,
    127,  64, 127, 127, 127,   0,   1,   2,   3,   4,
      5,   6,   7,   8,   9,  10,  11,  12,  13,  14,
     15,  16,  17,  18,  19,  20,  21,  22,  23,  24,
     25, 127, 127, 127, 127, 127, 127,  26,  27,  28,
     29,  30,  31,  32,  33,  34,  35,  36,  37,  38,
     39,  40,  41,  42,  43,  44,  45,  46,  47,  48,
     49,  50,  51, 127, 127, 127, 127, 127
	};



    for( i = j = n = 0; i < slen; i++ )
    {
        if( ( slen - i ) >= 2 &&
            src[i] == '\r' && src[i + 1] == '\n' )
            continue;

        if( src[i] == '\n' )
            continue;

        if( src[i] == '=' && ++j > 2 )
            return( POLARSSL_ERR_BASE64_INVALID_CHARACTER );

        if( src[i] > 127 || base64_dec_map[src[i]] == 127 )
            return( POLARSSL_ERR_BASE64_INVALID_CHARACTER );

        if( base64_dec_map[src[i]] < 64 && j != 0 )
            return( POLARSSL_ERR_BASE64_INVALID_CHARACTER );

        n++;
    }

    if( n == 0 )
        return( 0 );

    n = ((n * 6) + 7) >> 3;

    if( *dlen < n )
    {
        *dlen = n;
        return( POLARSSL_ERR_BASE64_BUFFER_TOO_SMALL );
    }

   for( j = 3, n = x = 0, p = dst; i > 0; i--, src++ )
   {
        if( *src == '\r' || *src == '\n' )
            continue;

        j -= ( base64_dec_map[*src] == 64 );
        x  = (x << 6) | ( base64_dec_map[*src] & 0x3F );

        if( ++n == 4 )
        {
            n = 0;
            if( j > 0 ) *p++ = (unsigned char)( x >> 16 );
            if( j > 1 ) *p++ = (unsigned char)( x >>  8 );
            if( j > 2 ) *p++ = (unsigned char)( x       );
        }
    }

    *dlen = p - dst;

    return( 0 );
}

int asn1_get_len( unsigned char **p,unsigned char *end,int *len )
{
    if( ( end - *p ) < 1 )
        return( POLARSSL_ERR_ASN1_OUT_OF_DATA );

    if( ( **p & 0x80 ) == 0 )
        *len = *(*p)++;
    else
    {
        switch( **p & 0x7F )
        {
        case 1:
            if( ( end - *p ) < 2 )
                return( POLARSSL_ERR_ASN1_OUT_OF_DATA );

            *len = (*p)[1];
            (*p) += 2;
            break;

        case 2:
            if( ( end - *p ) < 3 )
                return( POLARSSL_ERR_ASN1_OUT_OF_DATA );

            *len = ( (*p)[1] << 8 ) | (*p)[2];
            (*p) += 3;
            break;

        default:
            return( POLARSSL_ERR_ASN1_INVALID_LENGTH );
            break;
        }
    }

    if( *len > (int) ( end - *p ) )
        return( POLARSSL_ERR_ASN1_OUT_OF_DATA );

    return( 0 );
}

int asn1_get_tag( unsigned char **p,unsigned char *end,int *len, int tag )
{
    if( ( end - *p ) < 1 )
        return( POLARSSL_ERR_ASN1_OUT_OF_DATA );

    if( **p != tag )
        return( POLARSSL_ERR_ASN1_UNEXPECTED_TAG );

    (*p)++;

    return( asn1_get_len( p, end, len ) );
}

int asn1_get_int( unsigned char **p,unsigned char *end,int *val )
{
    int ret, len;

    if( ( ret = asn1_get_tag( p, end, &len, POLARSSL_ASN1_INTEGER  ) ) != 0 )
        return( ret );

    if( len > (int) sizeof( int ) || ( **p & 0x80 ) != 0 )
        return( POLARSSL_ERR_ASN1_INVALID_LENGTH );

    *val = 0;

    while( len-- > 0 )
    {
        *val = ( *val << 8 ) | **p;
        (*p)++;
    }

    return( 0 );
}

int asn1_get_mpi( unsigned char **p,unsigned char *end, mpi *X)
{
    int ret, len;

    if( ( ret = asn1_get_tag( p, end, &len, POLARSSL_ASN1_INTEGER ) ) != 0 )
        return( ret );

    ret = mpi_read_binary( X, *p, len );

    *p += len;

    return( ret );
}

int b2bn(mpi * X, unsigned char ** buf) 
{
	int tmp;
	tmp = mpi_size(X);

	if (mpi_write_binary(X, (*buf)+4, tmp)) {
		//printf("b2bn wrong!\n");
		return 1;
	}
	*((int *)(*buf)) = tmp;
	(*buf) = (*buf)+tmp+4;
	return 0;
}

/*
 * Load all data from a file into a given buffer.
 */
int load_file( char *path, unsigned char **buf,  int *n )
{
    FILE *f;

    if( ( f = fopen( path, "rb" ) ) == 0 )
        return( 1 );

    fseek( f, 0, SEEK_END );
    *n = (int) ftell( f );
    fseek( f, 0, SEEK_SET );

    if( ( *buf = (unsigned char *) malloc( *n + 1 ) ) == 0 )
        return( 1 );

    if( fread( *buf, 1, *n, f ) != *n )
    {
        fclose( f );
        free( *buf );
        return( 1 );
    }

    fclose( f );

    (*buf)[*n] = '\0';

    return( 0 );
}

int x509parse_keyfile( rsa_context *rsa, char *path, char *pwd )
{
    int ret;
    int n;
    unsigned char *buf;

    if ( load_file( path, &buf, &n ) )
        return( 1 );

    if( pwd == 0 )
        ret = x509parse_key( rsa, buf, (int) n, 0, 0 );
    else
        ret = x509parse_key( rsa, buf, (int) n, 0, 0 );

    memset( buf, 0, n + 1 );
    free( buf );

    return( ret );
}

/*
 * Parse a private RSA key
 */
int x509parse_key( rsa_context *rsa, unsigned char *buf, int buflen,
                                     unsigned char *pwd, int pwdlen )
{
    int ret, len, enc;
    unsigned char *s1, *s2;
    unsigned char *p, *end;
//#if defined(POLARSSL_DES_C) && defined(POLARSSL_MD5_C)
//    unsigned char des3_iv[8];
//#else
//    ((void) pwd);
//    ((void) pwdlen);
//#endif

    s1 = (unsigned char *) strstr( (char *) buf,
        "-----BEGIN RSA PRIVATE KEY-----" );

    if( s1 != 0 )
    {
        s2 = (unsigned char *) strstr( (char *) buf,
            "-----END RSA PRIVATE KEY-----" );

        if( s2 == 0 || s2 <= s1 )
            return( POLARSSL_ERR_X509_KEY_INVALID_PEM );

        s1 += 31;
        if( *s1 == '\r' ) s1++;
        if( *s1 == '\n' ) s1++;
            else return( POLARSSL_ERR_X509_KEY_INVALID_PEM );

        enc = 0;

        if( memcmp( s1, "Proc-Type: 4,ENCRYPTED", 22 ) == 0 )
        {
//#if defined(POLARSSL_DES_C) && defined(POLARSSL_MD5_C)
//            enc++;
//
//            s1 += 22;
//            if( *s1 == '\r' ) s1++;
//            if( *s1 == '\n' ) s1++;
//                else return( POLARSSL_ERR_X509_KEY_INVALID_PEM );
//
//            if( memcmp( s1, "DEK-Info: DES-EDE3-CBC,", 23 ) != 0 )
//                return( POLARSSL_ERR_X509_KEY_UNKNOWN_ENC_ALG );
//
//            s1 += 23;
//            if( x509_get_iv( s1, des3_iv ) != 0 )
//                return( POLARSSL_ERR_X509_KEY_INVALID_ENC_IV );
//
//            s1 += 16;
//            if( *s1 == '\r' ) s1++;
//            if( *s1 == '\n' ) s1++;
//                else return( POLARSSL_ERR_X509_KEY_INVALID_PEM );
//#else
            return( POLARSSL_ERR_X509_FEATURE_UNAVAILABLE );
//#endif
        }

        len = 0;
        ret = base64_decode( 0, &len, s1, s2 - s1 );

        if( ret == POLARSSL_ERR_BASE64_INVALID_CHARACTER )
            return( ret | POLARSSL_ERR_X509_KEY_INVALID_PEM );

        if( ( buf = (unsigned char *) malloc( len ) ) == 0 )
            return( 1 );

        if( ( ret = base64_decode( buf, &len, s1, s2 - s1 ) ) != 0 )
        {
            free( buf );
            return( ret | POLARSSL_ERR_X509_KEY_INVALID_PEM );
        }

        buflen = len;

        if( enc != 0 )
        {
//#if defined(POLARSSL_DES_C) && defined(POLARSSL_MD5_C)
//            if( pwd == 0 )
//            {
//                free( buf );
//                return( POLARSSL_ERR_X509_KEY_PASSWORD_REQUIRED );
//            }
//
//            x509_des3_decrypt( des3_iv, buf, buflen, pwd, pwdlen );
//
//            if( buf[0] != 0x30 || buf[1] != 0x82 ||
//                buf[4] != 0x02 || buf[5] != 0x01 )
//            {
//                free( buf );
//                return( POLARSSL_ERR_X509_KEY_PASSWORD_MISMATCH );
//            }
//#else
            return( POLARSSL_ERR_X509_FEATURE_UNAVAILABLE );
//#endif
        }
    }

    memset( rsa, 0, sizeof( rsa_context ) );

    p = buf;
    end = buf + buflen;

    /*
     *  RSAPrivateKey ::= SEQUENCE {
     *      version           Version,
     *      modulus           INTEGER,  -- n
     *      publicExponent    INTEGER,  -- e
     *      privateExponent   INTEGER,  -- d
     *      prime1            INTEGER,  -- p
     *      prime2            INTEGER,  -- q
     *      exponent1         INTEGER,  -- d mod (p-1)
     *      exponent2         INTEGER,  -- d mod (q-1)
     *      coefficient       INTEGER,  -- (inverse of q) mod p
     *      otherPrimeInfos   OtherPrimeInfos OPTIONAL
     *  }
     */
    if( ( ret = asn1_get_tag( &p, end, &len,
           POLARSSL_ASN1_CONSTRUCTED | POLARSSL_ASN1_SEQUENCE ) ) != 0 )
    {
        if( s1 != 0 )
            free( buf );

        rsa_free( rsa );
        return( POLARSSL_ERR_X509_KEY_INVALID_FORMAT | ret );
    }

    end = p + len;

    if( ( ret = asn1_get_int( &p, end, &rsa->ver ) ) != 0 )
    {
        if( s1 != 0 )
            free( buf );

        rsa_free( rsa );
        return( POLARSSL_ERR_X509_KEY_INVALID_FORMAT | ret );
    }

    if( rsa->ver != 0 )
    {
        if( s1 != 0 )
            free( buf );

        rsa_free( rsa );
        return( ret | POLARSSL_ERR_X509_KEY_INVALID_VERSION );
    }

    if( ( ret = asn1_get_mpi( &p, end, &rsa->N  ) ) != 0 ||
        ( ret = asn1_get_mpi( &p, end, &rsa->E  ) ) != 0 ||
        ( ret = asn1_get_mpi( &p, end, &rsa->D  ) ) != 0 ||
        ( ret = asn1_get_mpi( &p, end, &rsa->P  ) ) != 0 ||
        ( ret = asn1_get_mpi( &p, end, &rsa->Q  ) ) != 0 ||
        ( ret = asn1_get_mpi( &p, end, &rsa->DP ) ) != 0 ||
        ( ret = asn1_get_mpi( &p, end, &rsa->DQ ) ) != 0 ||
        ( ret = asn1_get_mpi( &p, end, &rsa->QP ) ) != 0 )
    {
        if( s1 != 0 )
            free( buf );

        rsa_free( rsa );
        return( ret | POLARSSL_ERR_X509_KEY_INVALID_FORMAT );
    }

    rsa->len = mpi_size( &rsa->N );

    if( p != end )
    {
        if( s1 != 0 )
            free( buf );

        rsa_free( rsa );
        return( POLARSSL_ERR_X509_KEY_INVALID_FORMAT |
                POLARSSL_ERR_ASN1_LENGTH_MISMATCH );
    }

    if( ( ret = rsa_check_privkey( rsa ) ) != 0 )
    {
        if( s1 != 0 )
            free( buf );

        rsa_free( rsa );
        return( ret );
    }

    if( s1 != 0 )
        free( buf );

    return( 0 );
}


int get_privkey(char * path, unsigned char * buf, int * buflen)
{
	int len;
	rsa_context * key;
	unsigned char * tmp;

	//static_malloc_init();
	/* read key from PEM format key file, no DES pass phase */
	key = (rsa_context *) malloc (sizeof(rsa_context));
	rsa_init(key, 0, 0);
	x509parse_keyfile( key, path , 0);
	//printf("parse key file!\n");

	/* transform key to binary format */
	memset(buf, 0, 2048);
	tmp = buf;
	if (b2bn(&(key->N), &tmp)) goto clean;
	if (b2bn(&(key->E), &tmp)) goto clean;
	if (b2bn(&(key->D), &tmp)) goto clean;
	if (b2bn(&(key->P), &tmp)) goto clean;
	if (b2bn(&(key->Q), &tmp)) goto clean;
	if (b2bn(&(key->DP), &tmp)) goto clean;
	if (b2bn(&(key->DQ), &tmp)) goto clean;
	if (b2bn(&(key->QP), &tmp)) goto clean;

	/* output binary string length */
	len = tmp - buf;
	//printf("original length = %d", len);
	if (len != ((len>>4)<<4))
		len = (((len>>4)+1)<<4);
	//printf("padded length = %d\n", len);
	//printf("b2bn!\n");
	*buflen = len;

	/* clean up and exit */
	rsa_free(key);
	return 0;

clean:
	rsa_free(key);
	return 1;
} 
