#!/bin/sh

# script used for moving files to penssl-0.9.8l installation directory
# the files contain our change to openssl in order to build secure HTTPS web server

# copy SSCB 2 code (still need Makefile)
cp sscb2/* ~/openssl-0.9.8l/ssl/
cp openssl/s3_srvr.c ~/openssl-0.9.8l/ssl/
cp openssl/Makefile ~/openssl-0.9.8l/ssl/

# copy OpenSSL header file
cp openssl/ssl.h ~/openssl-0.9.8l/include/openssl/

# copy linker script
cp defaultld.ld ~/openssl-0.9.8l/

# copy build script
cp buildSSL.sh ~/openssl-0.9.8l/
