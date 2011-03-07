#!/bin/sh

# script used for moving files to penssl-0.9.8l installation directory
# the files contain our change to openssl in order to build secure HTTPS web server

# copy SSCB 2 code (still need Makefile)
cp sscb2/* ~/openssl-0.9.8l/ssl/
cp openssl/s3_srvr.c ~/openssl-0.9.8l/ssl/
cp openssl/Makefile ~/openssl-0.9.8l/ssl/

# copy OpenSSL header file
cp openssl/ssl.h ~/openssl-0.9.8l/include/openssl/
cp openssl/sscb2.h ~/openssl-0.9.8l/ssl/
rm -f ~/openssl-0.9.8l/include/openssl/sscb2.h
ln -s ../../ssl/sscb2.h ~/openssl-0.9.8l/include/openssl/sscb2.h

# copy linker script
cp defaultld.ld ~/openssl-0.9.8l/

# copy build script
cp buildSSL.sh ~/openssl-0.9.8l/

# change the openssl Makefile to use our linker script
sed 's/^SHARED_LDFLAGS=.*/SHARED_LDFLAGS=-T defaultld.ld/' ~/openssl-0.9.8l/Makefile > new
mv new ~/openssl-0.9.8l/Makefile
