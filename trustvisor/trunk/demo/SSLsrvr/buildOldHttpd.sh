#!/bin/sh

rm /lib/libssl.so.0.9.8
ln -s /usr/local/ssl/lib/libssl.so.0.9.8 /lib/libssl.so.0.9.8
rm /lib/libssl.so
ln -s /lib/libssl.so.0.9.8 /lib/libssl.so
rm /lib/libcrypto.so.0.9.8
ln -s /usr/local/ssl/lib/libcrypto.so.0.9.8 /lib/libcrypto.so.0.9.8
rm /lib/libcrypto.so
ln -s /lib/libcrypto.so.0.9.8 /lib/libcrypto.so
rm /usr/include/openssl
ln -s /usr/local/ssl/include/openssl /usr/include/openssl

make clean
make > 1.txt
objdump -D ~/newhttpd/.libs/httpd > httpd.D
