#!/bin/sh
command=$1
op_link() {
	rm /lib/libssl.so.0.9.8
	ln -s /usr/local/nssl/lib/libssl.so.0.9.8 /lib/libssl.so.0.9.8
	rm /lib/i686/cmov/libssl.so.0.9.8
	ln -s /usr/local/nssl/lib/libssl.so.0.9.8 /lib/i686/cmov/libssl.so.0.9.8
	rm /lib/libssl.so
	ln -s /lib/libssl.so.0.9.8 /lib/libssl.so
	rm /lib/libcrypto.so.0.9.8
	ln -s /usr/local/nssl/lib/libcrypto.so.0.9.8 /lib/libcrypto.so.0.9.8
	rm /lib/i686/cmov/libcrypto.so.0.9.8
	ln -s /usr/local/nssl/lib/libcrypto.so.0.9.8 /lib/i686/cmov/libcrypto.so.0.9.8
	rm /lib/libcrypto.so
	ln -s /lib/libcrypto.so.0.9.8 /lib/libcrypto.so
	rm /usr/include/openssl
	ln -s /usr/local/nssl/include/openssl /usr/include/openssl
	export LD_BIND_NOW="1"
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


