/**
   ssl_rec.c


   Copyright (C) 1999-2000 RTFM, Inc.
   All Rights Reserved

   This package is a SSLv3/TLS protocol analyzer written by Eric Rescorla
   <ekr@rtfm.com> and licensed by RTFM, Inc.

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions
   are met:
   1. Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
   3. All advertising materials mentioning features or use of this software
      must display the following acknowledgement:
   
      This product includes software developed by Eric Rescorla for
      RTFM, Inc.

   4. Neither the name of RTFM, Inc. nor the name of Eric Rescorla may be
      used to endorse or promote products derived from this
      software without specific prior written permission.

   THIS SOFTWARE IS PROVIDED BY ERIC RESCORLA AND RTFM, INC. ``AS IS'' AND
   ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
   IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
   ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
   FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
   DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
   OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
   HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
   LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
   OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY SUCH DAMAGE.

   $Id: ssl_rec.c,v 1.3 2000/11/03 06:38:06 ekr Exp $


   ekr@rtfm.com  Wed Aug 18 15:46:57 1999
 */


static char *RCSSTRING="$Id: ssl_rec.c,v 1.3 2000/11/03 06:38:06 ekr Exp $";

#include "network.h"
#include "ssl_h.h"
#include "sslprint.h"
#include "ssl.enums.h"
#include "ssldecode.h"
#include "ssl_rec.h"

struct ssl_rec_decoder_ {
     SSL_CipherSuite *cs;
     Data *mac_key;
     UINT4 seq;
};


static char *digests[]={
     "MD5",
     "SHA1"
};

static char *ciphers[]={
     "DES",
     "DES3",
     "RC4",
     "RC2",
     "IDEA"
};


static int tls_check_mac PROTO_LIST((ssl_rec_decoder *d,int ct,
  int ver,UCHAR *data,UINT4 datalen,UCHAR *mac));
static int fmt_seq PROTO_LIST((UINT4 num,UCHAR *buf));

int ssl_create_rec_decoder(dp,cs,mk,sk,iv)
  ssl_rec_decoder **dp;
  SSL_CipherSuite *cs;
  UCHAR *mk;
  UCHAR *sk;
  UCHAR *iv;
  {
    int r,_status;
    ssl_rec_decoder *dec=0;
    
    *dp=dec;
    _status=0;
  abort:
    if(_status){
      ssl_destroy_rec_decoder(&dec);
    }
    return(_status);
  }

int ssl_destroy_rec_decoder(dp)
  ssl_rec_decoder **dp;
  {
    ssl_rec_decoder *d;
    
    if(!dp || !*dp)
      return(0);
    d=*dp;

    r_data_destroy(&d->mac_key);

    *dp=0;
    return(0);
  }
    
int ssl_decode_rec_data(ssl,d,ct,version,in,inl,out,outl)
  ssl_obj *ssl;
  ssl_rec_decoder *d;
  int ct;
  int version;
  UCHAR *in;
  int inl;
  UCHAR *out;
  int *outl;
  {
    return(0);
  }
    

#define MSB(a) ((a>>8)&0xff)
#define LSB(a) (a&0xff)
