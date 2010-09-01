#!/bin/sh
# build slb and examine the plt entry of bar()
rm /lib/libssl.so.0.9.8
ln -s /usr/local/nssl/lib/libssl.so.0.9.8 /lib/libssl.so.0.9.8
rm /lib/libssl.so
ln -s /lib/libssl.so.0.9.8 /lib/libssl.so
rm /lib/libcrypto.so.0.9.8
ln -s /usr/local/nssl/lib/libcrypto.so.0.9.8 /lib/libcrypto.so.0.9.8
rm /lib/libcrypto.so
ln -s /lib/libcrypto.so.0.9.8 /lib/libcrypto.so
rm /usr/include/openssl
ln -s /usr/local/nssl/include/openssl /usr/include/openssl
make clean
make > 1.txt
objdump -D ~/newhttpd/.libs/httpd > httpd.D
echo \#define MAGIC_ADDR 0x`grep -A1 "<get_addr@plt>:" httpd.D | tail -1 | cut -d x -f 2` > ~/newhttpd/modules/ssl/magic_addr.h
objdump -D /usr/local/nssl/lib/libssl.so.0.9.8 > nlib.D
echo \#define THUNK_ADDR 0x`grep "<__i686.get_pc_thunk.bx>:" nlib.D | cut -c 1-8` >> ~/newhttpd/modules/ssl/magic_addr.h
echo \#define ENTRY_ADDR 0x`grep "<sscb2>:" nlib.D | cut -c 1-8` >> ~/newhttpd/modules/ssl/magic_addr.h
cat ~/newhttpd/modules/ssl/magic_addr.h
make clean
make > 2.txt
echo ENTRY_ADDR 0x`grep "<sscb1>:" httpd.D | cut -c 1-8` 
echo TEXT_ADDR 0x`grep "<scode_seal>:" httpd.D | cut -c 1-8` 
echo DATA_ADDR 0x`grep "<sdatajunk>:" httpd.D | cut -c 1-8`
echo PARAM_ADDR 0x`grep "<paramjunk>:" httpd.D | cut -c 1-8`
echo STACK_ADDR 0x`grep "<stackjunk>:" httpd.D | cut -c 1-8`
