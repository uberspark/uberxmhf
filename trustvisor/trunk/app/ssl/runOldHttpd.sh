#!/bin/sh
# script for running vanilla apache with vanilla openssl
# ./vanillarun.sh single	--  run one process apache
# ./vanillarun.sh multi		--  run prefork apache
# ./vanillarun.sh debug		--  use gdb to run one process apache
# ./vanillarun.sh link 		--  link apache with vanilla openssl


# Need to first install openssl
# ./config shared; make; make install
# then install apache
# ./configure --enable-ssl=static --with-ssl=/usr/local/ssl
# copy vanillarun.sh to the home directory of apache and run

command=$1
op_link() {
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
}

op_single() {
	./httpd -X
}

op_multi() {
	./httpd 
}

op_debug() {
	gdb .libs/httpd
}

case "$command" in
	single)
		op_link
		op_single
		;;

	multi)
		op_link
		op_multi
		;;

	debug)
		op_link
		op_debug
		;;

	link)
		op_link
		;;

	*)
		echo "Unknown command: $command"
		exit 1
esac


