#!/bin/sh

# script used for moving files to httpd-2.2.14 or openssl-0.9.8l installation directory
# the files contain our change to httpd and openssl in order to build secure HTTPS web server

# remember to build mod_ssl statically with httpd
# ./configure --enable-ssl=static --with-ssl=/usr/local/ssl/

# copy mod_ssl code
cp httpd/* ~/httpd-2.2.14/modules/ssl/
mv ~/httpd-2.2.14/modules/ssl/prefork.c ~/httpd-2.2.14/server/mpm/prefork/
# copy SSCB 1 code (still need Makefile)
cp sscb1/* ~/httpd-2.2.14/modules/ssl

# copy SSCB 2 code (still need Makefile)
#cp sscb2s/* ~/openssl-0.9.8l/ssl/
#cp openssl/s3_srvr.c ~/openssl-0.9.8l/ssl/
#cp openssl/Makefile ~/openssl-0.9.8l/ssl/

# copy OpenSSL header file
#cp openssl/ssl.h /usr/include/openssl/
#cp openssl/ssl.h /include/openssl/
#cp openssl/ssl.h /usr/local/ssl/include/openssl/

#cp openssl/ssl.h ~/openssl-0.9.8l/include/openssl/

# copy linker script
#cp defaultld.ld ~/openssl-0.9.8l/
cp defaultld.ld ~/httpd-2.2.14/
cp run.sh ~/httpd-2.2.14/
cd ~/httpd-2.2.14/
