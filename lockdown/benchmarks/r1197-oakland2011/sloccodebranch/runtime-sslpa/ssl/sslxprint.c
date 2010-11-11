/**
   sslxprint.c


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

   $Id: sslxprint.c,v 1.3 2000/11/03 06:38:06 ekr Exp $


   ekr@rtfm.com  Thu Mar 25 21:17:16 1999
 */


static char *RCSSTRING="$Id: sslxprint.c,v 1.3 2000/11/03 06:38:06 ekr Exp $";

#include "network.h"
#include "ssl_h.h"
#include "sslprint.h"
#include "ssl.enums.h"

#define BUFSIZE 1024

static int sslx__print_dn PROTO_LIST((ssl_obj *ssl,char *x));

int sslx_print_certificate(ssl,data,pf)
  ssl_obj *ssl;
  Data *data;
  int pf;
  {
    UCHAR *d;
    int _status;
    
        P_(pf){
          exdump(ssl,"certificate",data);
        }

    _status=0;
  abort:
    return(_status);
  }  

int sslx_print_dn(ssl,data,pf)
  ssl_obj *ssl;
  Data *data;
  int pf;
  {
    UCHAR buf[BUFSIZE];
    int _status;
    UCHAR *d=data->data;
    
    P_(pf){
	exdump(ssl,0,data);
    }

    _status=0;
  abort:
    return(_status);
  }

static int sslx__print_dn(ssl,x)
  ssl_obj *ssl;
  char *x;
  {
    char *slash;

    if(*x=='/') x++;
    
    while (x){
      if(slash=strchr(x,'/')){
	*slash=0;
      }

      explain(ssl,"%s\n",x);

      x=slash?slash+1:0;
    };

    return(0);
  }

