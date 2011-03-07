#!/bin/sh

# script used for moving files to newhttpd or openssl-0.9.8l installation directory
# the files contain our change to httpd and openssl in order to build secure HTTPS web server

# remember to build mod_ssl statically with httpd
# ./configure --enable-ssl=static --with-ssl=/usr/local/ssl/

# copy mod_ssl code
cp httpd/* ~/newhttpd/modules/ssl/
mv ~/newhttpd/modules/ssl/prefork.c ~/newhttpd/server/mpm/prefork/
# copy SSCB 1 code (still need Makefile)
cp sscb1/* ~/newhttpd/modules/ssl

# copy linker script
cp defaultld.ld ~/newhttpd/
cp buildNewHttpd.sh ~/newhttpd/
cp runNewHttpd.sh ~/newhttpd/
