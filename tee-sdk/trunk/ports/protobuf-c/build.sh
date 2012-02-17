#!/bin/sh

if [ -z "$HOST" ]
then
	HOST=i586-tsvc
fi

if [ -z "$BUILD" ]
then
	BUILD=i686-pc-linux-gnu
fi

if [ -z "$PREFIX" ]
then
	PREFIX=/usr/local/$HOST/usr
fi

cd protobuf-c-0.15
./configure --prefix=${PREFIX} --host=${HOST} --build=${BUILD} --disable-protoc
make
make install

