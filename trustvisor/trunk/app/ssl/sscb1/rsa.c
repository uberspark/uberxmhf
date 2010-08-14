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
#include "string.h"

void rsa_init( rsa_context *ctx,
               int padding,
               int hash_id)
{
    memset( ctx, 0, sizeof( rsa_context ) );

    ctx->padding = padding;
    ctx->hash_id = hash_id;
}

/*
 * Check a private RSA key
 */
int rsa_check_privkey( rsa_context *ctx )
{
	int ret;
	mpi PQ, DE, P1, Q1, H, I, G;

	//if( ( ret = rsa_check_pubkey( ctx ) ) != 0 )
	//    return( ret );

	mpi_init( &PQ );
	mpi_init( &DE );
	mpi_init( &P1 );
	mpi_init( &Q1 );
	mpi_init( &H );
	mpi_init( &I );
	mpi_init( &G );

	MPI_CHK( mpi_mul_mpi( &PQ, &ctx->P, &ctx->Q ) );
	MPI_CHK( mpi_mul_mpi( &DE, &ctx->D, &ctx->E ) );
	MPI_CHK( mpi_sub_int( &P1, &ctx->P, 1 ) );
	MPI_CHK( mpi_sub_int( &Q1, &ctx->Q, 1 ) );
	MPI_CHK( mpi_mul_mpi( &H, &P1, &Q1 ) );
	MPI_CHK( mpi_mod_mpi( &I, &DE, &H  ) );
	MPI_CHK( mpi_gcd( &G, &ctx->E, &H  ) );

	if( mpi_cmp_mpi( &PQ, &ctx->N ) == 0 &&
			mpi_cmp_int( &I, 1 ) == 0 &&
			mpi_cmp_int( &G, 1 ) == 0 )
	{
		mpi_free( &PQ );
		mpi_free( &DE );
		mpi_free( &P1 );
		mpi_free( &Q1 );
		mpi_free( &H );
		mpi_free( &I );
		mpi_free( &G );

		return( 0 );
	}

cleanup:
	mpi_free( &PQ );
	mpi_free( &DE );
	mpi_free( &P1 );
	mpi_free( &Q1 );
	mpi_free( &H );
	mpi_free( &I );
	mpi_free( &G );

	return( XYSSL_ERR_RSA_KEY_CHECK_FAILED | ret );
}

/*
 * Free the components of an RSA key
 */
void rsa_free( rsa_context *ctx )
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
