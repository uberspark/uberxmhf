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

/*
 *  The RSA public-key cryptosystem
 *
 *  Copyright (C) 2006-2007  Christophe Devine
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
/*
 *  RSA was designed by Ron Rivest, Adi Shamir and Len Adleman.
 *
 *  http://theory.lcs.mit.edu/~rivest/rsapaper.pdf
 *  http://www.cacr.math.uwaterloo.ca/hac/about/chap8.pdf
 */

#include "rsa.h"
#include "puttymem.h"

/* Init rsa context */
__attribute__ ((section (".stext"))) void rsa_init( rsa_context *ctx,
               int padding,
               int hash_id)
{
    vmemset( ctx, 0, sizeof( rsa_context ) );

    ctx->padding = padding;
    ctx->hash_id = hash_id;
}

/*
 * Do an RSA private key operation
 */
__attribute__ ((section (".stext"))) int rsa_private( rsa_context *ctx,
		unsigned char *input,
		unsigned char *output )
{
	int ret, olen;
	mpi T, T1, T2;

	mpi_init( &T );
	mpi_init( &T1);
	mpi_init( &T2);

	MPI_CHK( mpi_read_binary( &T, input, ctx->len ) );

	if( mpi_cmp_mpi( &T, &ctx->N ) >= 0 )
	{
		mpi_free( &T );
		return( XYSSL_ERR_RSA_BAD_INPUT_DATA );
	}

#if 0
	MPI_CHK( mpi_exp_mod( &T, &T, &ctx->D, &ctx->N, &ctx->RN ) );
#else
	/*
	 * faster decryption using the CRT
	 *
	 * T1 = input ^ dP mod P
	 * T2 = input ^ dQ mod Q
	 */
	MPI_CHK( mpi_exp_mod( &T1, &T, &ctx->DP, &ctx->P, &ctx->RP ) );
	MPI_CHK( mpi_exp_mod( &T2, &T, &ctx->DQ, &ctx->Q, &ctx->RQ ) );

	/*
	 * T = (T1 - T2) * (Q^-1 mod P) mod P
	 */
	MPI_CHK( mpi_sub_mpi( &T, &T1, &T2 ) );
	MPI_CHK( mpi_mul_mpi( &T1, &T, &ctx->QP ) );
	MPI_CHK( mpi_mod_mpi( &T, &T1, &ctx->P ) );

	/*
	 * output = T2 + T * Q
	 */
	MPI_CHK( mpi_mul_mpi( &T1, &T, &ctx->Q ) );
	MPI_CHK( mpi_add_mpi( &T, &T2, &T1 ) );
#endif

	olen = ctx->len;
	MPI_CHK( mpi_write_binary( &T, output, olen ) );

cleanup:

	mpi_free( &T );
	mpi_free( &T1);
	mpi_free( &T2);

	if( ret != 0 )
		return( XYSSL_ERR_RSA_PRIVATE_FAILED | ret );

	return( 0 );
}

/*
 * Add the message padding, then do an RSA operation
 */
__attribute__ ((section (".stext"))) int rsa_pkcs1_encrypt( rsa_context *ctx,
		int mode, int  ilen,
		unsigned char *input,
		unsigned char *output )
{
	int nb_pad, olen;
	unsigned char *p = output;

	olen = ctx->len;

	switch( ctx->padding )
	{
		case RSA_PKCS_V15:

			if( ilen < 0 || olen < ilen + 11 )
				return( XYSSL_ERR_RSA_BAD_INPUT_DATA );

			nb_pad = olen - 3 - ilen;

			*(p++) = 0;
			*(p++) = 1;
			//*p++ = RSA_CRYPT;

			while( nb_pad-- > 0 )
			{
//				do {
//					*p = random_byte();
//					//*p = (unsigned char) rand();
//				} while( *p == 0 );
				//p++;
				*(p++) = 0xff;
			}
			*p++ = 0;
			vmemcpy( p, input, ilen );
			break;

		default:

			return( XYSSL_ERR_RSA_INVALID_PADDING );
	}

	return (rsa_private(ctx, output, output));
//	return( ( mode == RSA_PUBLIC )
//			? rsa_public(  ctx, output, output )
//			: rsa_private( ctx, output, output ) );
}

/*
 * Free the components of an RSA key
 */
__attribute__ ((section (".stext"))) void rsa_free( rsa_context *ctx )
{
	mpi_free( &ctx->RQ);
	mpi_free( &ctx->RP);
	mpi_free( &ctx->RN);
	mpi_free( &ctx->QP);
	mpi_free( &ctx->DQ);
	mpi_free( &ctx->DP);
	mpi_free( &ctx->Q);
	mpi_free( &ctx->P);
	mpi_free(  &ctx->D);
	mpi_free( &ctx->E);
	mpi_free( &ctx->N );
}

__attribute__ ((section (".stext"))) int rsa_private_encrypt( int size, unsigned char* input, unsigned char* output, rsa_context * key, int ignore ) 
{ 
	if( !rsa_pkcs1_encrypt( key, RSA_PRIVATE, size, input, output ) ) 
		return rsa_size(key); 
	else 
		return -1; 
}

__attribute__ ((section (".stext"))) int bn2b(unsigned char ** buf, mpi * X)
{
	int tmp;
	tmp = *((int *)(*buf));

	if (mpi_read_binary(X, (*buf)+4, tmp)) {
		return 1;
	}
	(*buf) = (*buf)+tmp+4;
	return 0;
}

