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

/* header file for parse.c */

/* BASE64 Error code */
#define POLARSSL_ERR_BASE64_BUFFER_TOO_SMALL               0x0010
#define POLARSSL_ERR_BASE64_INVALID_CHARACTER              0x0012


/*
 * ASN1 Error codes
 *
 * These error codes will be OR'ed to X509 error codes for
 * higher error granularity.
 */
#define POLARSSL_ERR_ASN1_OUT_OF_DATA                      0x0014
#define POLARSSL_ERR_ASN1_UNEXPECTED_TAG                   0x0016
#define POLARSSL_ERR_ASN1_INVALID_LENGTH                   0x0018
#define POLARSSL_ERR_ASN1_LENGTH_MISMATCH                  0x001A
#define POLARSSL_ERR_ASN1_INVALID_DATA                     0x001C


/*
 * X509 Error codes
 */
#define POLARSSL_ERR_X509_FEATURE_UNAVAILABLE              -0x0020
#define POLARSSL_ERR_X509_CERT_INVALID_PEM                 -0x0040
#define POLARSSL_ERR_X509_CERT_INVALID_FORMAT              -0x0060
#define POLARSSL_ERR_X509_CERT_INVALID_VERSION             -0x0080
#define POLARSSL_ERR_X509_CERT_INVALID_SERIAL              -0x00A0
#define POLARSSL_ERR_X509_CERT_INVALID_ALG                 -0x00C0
#define POLARSSL_ERR_X509_CERT_INVALID_NAME                -0x00E0
#define POLARSSL_ERR_X509_CERT_INVALID_DATE                -0x0100
#define POLARSSL_ERR_X509_CERT_INVALID_PUBKEY              -0x0120
#define POLARSSL_ERR_X509_CERT_INVALID_SIGNATURE           -0x0140
#define POLARSSL_ERR_X509_CERT_INVALID_EXTENSIONS          -0x0160
#define POLARSSL_ERR_X509_CERT_UNKNOWN_VERSION             -0x0180
#define POLARSSL_ERR_X509_CERT_UNKNOWN_SIG_ALG             -0x01A0
#define POLARSSL_ERR_X509_CERT_UNKNOWN_PK_ALG              -0x01C0
#define POLARSSL_ERR_X509_CERT_SIG_MISMATCH                -0x01E0
#define POLARSSL_ERR_X509_CERT_VERIFY_FAILED               -0x0200
#define POLARSSL_ERR_X509_KEY_INVALID_PEM                  -0x0220
#define POLARSSL_ERR_X509_KEY_INVALID_VERSION              -0x0240
#define POLARSSL_ERR_X509_KEY_INVALID_FORMAT               -0x0260
#define POLARSSL_ERR_X509_KEY_INVALID_ENC_IV               -0x0280
#define POLARSSL_ERR_X509_KEY_UNKNOWN_ENC_ALG              -0x02A0
#define POLARSSL_ERR_X509_KEY_PASSWORD_REQUIRED            -0x02C0
#define POLARSSL_ERR_X509_KEY_PASSWORD_MISMATCH            -0x02E0
#define POLARSSL_ERR_X509_POINT_ERROR                      -0x0300
#define POLARSSL_ERR_X509_VALUE_TO_LENGTH                  -0x0320

/*
 * DER constants
 */
#define POLARSSL_ASN1_BOOLEAN                 0x01
#define POLARSSL_ASN1_INTEGER                 0x02
#define POLARSSL_ASN1_BIT_STRING              0x03
#define POLARSSL_ASN1_OCTET_STRING            0x04
#define POLARSSL_ASN1_NULL                    0x05
#define POLARSSL_ASN1_OID                     0x06
#define POLARSSL_ASN1_UTF8_STRING             0x0C
#define POLARSSL_ASN1_SEQUENCE                0x10
#define POLARSSL_ASN1_SET                     0x11
#define POLARSSL_ASN1_PRINTABLE_STRING        0x13
#define POLARSSL_ASN1_T61_STRING              0x14
#define POLARSSL_ASN1_IA5_STRING              0x16
#define POLARSSL_ASN1_UTC_TIME                0x17
#define POLARSSL_ASN1_UNIVERSAL_STRING        0x1C
#define POLARSSL_ASN1_BMP_STRING              0x1E
#define POLARSSL_ASN1_PRIMITIVE               0x00
#define POLARSSL_ASN1_CONSTRUCTED             0x20
#define POLARSSL_ASN1_CONTEXT_SPECIFIC        0x80

int get_privkey(char * path, unsigned char * buf, int * buflen);

