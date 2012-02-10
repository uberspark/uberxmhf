#!/bin/bash

BASEDIR=$(dirname $0)

echo "$0 initializing" >&2

MACADDR=$(./getmacaddr.sh)
TIMESTAMP=$(./gettimestamp.sh)

TESTDIR=$MACADDR/$TIMESTAMP
mkdir -p $TESTDIR
pushd $TESTDIR

echo "$0 initializing" | tee shell.log
echo "Host identifier: $MACADDR" | tee shell.log
echo "Time stamp: $TIMESTAMP" | tee shell.log

echo "Fetching http://10.0.0.1/test" | tee shell.log
wget http://10.0.0.1/test
chmod +x test
echo "Invoking ./test" | tee shell.log
./test 2>&1 | tee shell.log


popd
scp -o StrictHostKeyChecking=no -r $MACADDR logger@10.0.0.1: \
  | tee shell.log

echo "... Success!"

expect alldone.exp ttyS0

exit 0

