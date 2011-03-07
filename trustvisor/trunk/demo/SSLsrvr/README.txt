Application: 
Use TrustVisor to protect the private key of HTTPS server

Requirement:
1. httpd-2.2.14 tar ball
2. openssl-0.9.8l tar ball
3. all the other scripts, files and directories under this directory

Process:
*********************************
	Install OpenSSL
*********************************
1. decompress openssl tar ball to ~/
2. go to ~/openssl-0.9.8l/
3. run "./config shared --prefix=/usr/local/nssl --openssldir=/usr/local/nssl no-threads" (add "-fno-stack-protector" if you are using Ubuntu)
4. back to this directory 
5. run "./moveSSL.sh" to patch the OpenSSL source code
6. back to ~/openssl-0.9.8l/
7. run "sudo ./buildSSL.sh" to compile and install OpenSSL w/ our changes
   The installation will be put into /usr/local/nssl/

*********************************
	Install Apache
*********************************
1. decompress httpd tar ball to ~/
2. change the directory name from ~/httpd-2.2.14/to ~/newhttpd/
3. go to ~/newhttpd/
4. run "./configure --enable-ssl=static --with-ssl=/usr/local/nssl/ HTTPD_LDFLAGS="-T defaultld.ld" " (add "CFLAGS=-fno-stack-protector" if you are using Ubuntu)
5. back to this directory
6. run "./moveHttpd.sh" to patch the Apache source code
7. back to ~/newhttpd/
8. run "./buildNewHttpd.sh" to compile Apache source code
9. run "sudo make install" to install apache server

*********************************
	    Run Demo
*********************************
1. compile and install TrustVisor, reboot
2. start configuring Apache SSL server
	- edit /usr/local/apache2/conf/httpd.conf (e.g. site address), enable SSL module
	- generate SSL server key and certificate using Openssl
	openssl req -new -x509 -days 365 -sha1 -newkey rsa:2048 -nodes -keyout server.key -out server.crt
	- move server.key and server.crt to /usr/local/apache2/conf/
	- edit /usr/local/apache2/conf/extra/httpd-ssl.conf (e.g. site address)
3. go to ~/newhttpd/
4. run "./runNewHttpd.sh single" to start HTTPS server (single process)
5. find another machine and run "ab -n 1 -c 1 -f SSL3 https://......" to init
   an SSL connection 
6. run "./runNewHttpd.sh multi" to start HTTPS server (prefork multi-process)
7. use another machine to generate SSL connection similar to step 4.

*********************************
   Run Comparison Experiment
*********************************
1. install vanilla OpenSSL-0.9.8l to /usr/loca/ssl
2. decompress httpd tar ball to ~/ and change directory name to ~/oldhttpd/
3. go to ~/oldhttpd/
4. run "./configure --enable-ssl=static --with-ssl=/usr/local/ssl/ "
5. run "./buildOldHttpd.sh" to compile Apache source code
6. run "./runOldHttpd.sh [single|multi]" to start vanilla HTTPS server
7. run ab test suite on another machine to init SSL connection


