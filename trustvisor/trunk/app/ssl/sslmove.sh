#!/bin/sh

# script used for moving files to httpd-2.2.14 or openssl-0.9.8l installation directory
# the files contain our change to httpd and openssl in order to build secure HTTPS web server

# config openssl as follows:
# ./config shared --prefix=/usr/local/nssl --openssldir=/usr/local/nssl

# remember to build mod_ssl statically with httpd
# ./configure --enable-ssl=static --with-ssl=/usr/local/nssl/ HTTPD_LDFLAGS="-T defaultld.ld"

# copy mod_ssl code
#cp ssl/* ~/httpd-2.2.14/modules/ssl/

# copy SSCB 1 code (still need Makefile)
#cp sscb1/* ~/httpd-2.2.14/modules/ssl

# copy SSCB 2 code (still need Makefile)
cp sscb2/* ~/openssl-0.9.8l/ssl/
cp openssl/s3_srvr.c ~/openssl-0.9.8l/ssl/
cp openssl/Makefile ~/openssl-0.9.8l/ssl/

# copy OpenSSL header file
#cp openssl/ssl.h /usr/include/openssl/
#cp openssl/ssl.h /include/openssl/
#cp openssl/ssl.h /usr/local/ssl/include/openssl/

cp openssl/ssl.h ~/openssl-0.9.8l/include/openssl/

# copy linker script
cp defaultld.ld ~/openssl-0.9.8l/
#cp defaultld.ld ~/httpd-2.2.14/

cd ~/openssl-0.9.8l/
make
make install
objdump -D /usr/local/nssl/lib/libssl.so.0.9.8 > nlib.D
echo THUNK_ADDR 0x`grep "<__i686.get_pc_thunk.bx>:" nlib.D | cut -c 1-8` 
echo ENTRY_ADDR 0x`grep "<sscb2>:" nlib.D | cut -c 1-8` 
echo TEXT_ADDR 0x`grep "<scode_unseal>:" nlib.D | cut -c 1-8` 
echo DATA_ADDR 0x`grep "<sdatajunk2>:" nlib.D | cut -c 1-8`
echo PARAM_ADDR 0x`grep "<paramjunk2>:" nlib.D | cut -c 1-8`
echo STACK_ADDR 0x`grep "<stackjunk2>:" nlib.D | cut -c 1-8`
