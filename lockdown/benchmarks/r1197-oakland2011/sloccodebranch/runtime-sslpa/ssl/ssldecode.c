/**
   ssldecode.c


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

   $Id: ssldecode.c,v 1.9 2002/08/17 01:33:17 ekr Exp $


   ekr@rtfm.com  Thu Apr  1 09:54:53 1999
 */
#include <lockdown/types.h>
#include <lockdown/lockdown.h>
#include <lockdown/string.h>

#include "network.h"
#include "ssl_h.h"
#include "sslprint.h"
#include "ssl.enums.h"
#include "ssldecode.h"
#include "ssl_rec.h"
#include "r_assoc.h"
static char *RCSSTRING="$Id: ssldecode.c,v 1.9 2002/08/17 01:33:17 ekr Exp $";

#define PRF(ssl,secret,usage,rnd1,rnd2,out) (ssl->version==SSLV3_VERSION)? \
        ssl3_prf(ssl,secret,usage,rnd1,rnd2,out): \
        tls_prf(ssl,secret,usage,rnd1,rnd2,out)


static char *ssl_password;

extern UINT4 SSL_print_flags;

struct ssl_decode_ctx_ {
     char dummy;       /* Some compilers (Win32) don't like empty
                           structs */
#endif     
};

struct ssl_decoder_ {
     ssl_decode_ctx *ctx;
     Data *session_id;
     SSL_CipherSuite *cs;
     Data *client_random;
     Data *server_random;
     int ephemeral_rsa;
     Data *PMS;
     Data *MS;
     ssl_rec_decoder *c_to_s;
     ssl_rec_decoder *s_to_c;     
     ssl_rec_decoder *c_to_s_n;
     ssl_rec_decoder *s_to_c_n;
};



static int ssl_create_session_lookup_key PROTO_LIST((ssl_obj *ssl,
  UCHAR *id,UINT4 idlen,UCHAR **keyp,UINT4 *keyl));
int ssl_save_session PROTO_LIST((ssl_obj *ssl,ssl_decoder *d));
int ssl_restore_session PROTO_LIST((ssl_obj *ssl,ssl_decoder *d));

/*The password code is not thread safe*/
static int password_cb(char *buf,int num,int rwflag,void *userdata)
  {
    if(num<strlen(ssl_password)+1)
      return(0);

    strcpy(buf,ssl_password);
    return(strlen(ssl_password));
  }

int ssl_decode_ctx_create(dp,keyfile,pass)
  ssl_decode_ctx **dp;
  char *keyfile;
  char *pass;
  {
    return(0);
#endif
  }

int ssl_decoder_create(dp,ctx)
  ssl_decoder **dp;
  ssl_decode_ctx *ctx;
  {
    int _status;
    
    ssl_decoder *d=0;

    return 0;
#endif
  }

int ssl_decoder_destroy(dp)
  ssl_decoder **dp;
  {
    return(0);
  }

int ssl_set_client_random(d,msg,len)
  ssl_decoder *d;
  UCHAR *msg;
  int len;
  {
    return(0);
  }
      
int ssl_set_server_random(d,msg,len)
  ssl_decoder *d;
  UCHAR *msg;
  int len;
  {
    return(0);
  }

int ssl_set_client_session_id(d,msg,len)
  ssl_decoder *d;
  UCHAR *msg;
  int len;
  {
    return(0);
  }

int ssl_process_server_session_id(ssl,d,msg,len)
  ssl_obj *ssl;
  ssl_decoder *d;
  UCHAR *msg;
  int len;
  {
    return(0);
#endif      
  }
  
int ssl_process_change_cipher_spec(ssl,d,direction)
  ssl_obj *ssl;
  ssl_decoder *d;
  int direction;
  {
    return(0);
  }
int ssl_decode_record(ssl,dec,direction,ct,version,d)
  ssl_obj *ssl;
  ssl_decoder *dec;
  int direction;
  int ct;
  int version;
  Data *d;
  {
    ssl_rec_decoder *rd;
    UCHAR *out;
    int outl;
    int r,_status;
    UINT4 state;

    if(dec)
      rd=(direction==DIR_I2R)?dec->c_to_s:dec->s_to_c;
    else
      rd=0;
    state=(direction==DIR_I2R)?ssl->i_state:ssl->r_state;

    if(!rd){
      if(state & SSL_ST_SENT_CHANGE_CIPHER_SPEC){
        ssl->record_encryption=REC_CIPHERTEXT;
        return(SSL_NO_DECRYPT);
      }
      else {
        ssl->record_encryption=REC_PLAINTEXT;
        return(0);
      }
    }

    ssl->record_encryption=REC_CIPHERTEXT;        
    return(0);                                                  
#endif    
  }


static int ssl_create_session_lookup_key(ssl,id,idlen,keyp,keyl)
  ssl_obj *ssl;
  UCHAR *id;
  UINT4 idlen;
  UCHAR **keyp;
  UINT4 *keyl;
  {
    UCHAR *key=0;
    UINT4 l;
    int r,_status;

    l=idlen+strlen(ssl->server_name)+idlen+15; /* HOST + PORT + id */
    
    if(!(key=(UCHAR *)malloc(l)))
      ABORT(R_NO_MEMORY);
    *keyp=key;
    
    memcpy(key,id,idlen);
    *keyl=idlen;
    key+=idlen;
    
    snprintf(key, strlen(key), "%s:%d",ssl->server_name,ssl->server_port);
    *keyl+=strlen(key);

    _status=0;
  abort:
    return(_status);
  }
  
/* Look up the session id in the session cache and generate
   the appropriate keying material */
int ssl_restore_session(ssl,d)
  ssl_obj *ssl;
  ssl_decoder *d;
  {
    UCHAR *lookup_key=0;
    void *msv;
    Data *msd;
    int lookup_key_len;
    int r,_status;
    return(0);
#endif    
  }

/* Look up the session id in the session cache and generate
   the appropriate keying material */
int ssl_save_session(ssl,d)
  ssl_obj *ssl;
  ssl_decoder *d;
  {
    return(0);
#endif
  }

/* This only works with RSA because the other cipher suites
   offer PFS. Yuck. */
int ssl_process_client_key_exchange(ssl,d,msg,len)
  ssl_obj *ssl;
  ssl_decoder *d;
  UCHAR *msg;
  int len;
  {
    return 0;
#endif    
    
  }

