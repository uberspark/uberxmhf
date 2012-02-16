#!/bin/bash

BASEDIR=$(dirname $0)
LOGFILE=shell.log

echo "$0 initializing" >&2

MACADDR=$(./getmacaddr.sh)
TIMESTAMP=$(./gettimestamp.sh)

TESTDIR=$MACADDR/$TIMESTAMP
mkdir -p $TESTDIR
pushd $TESTDIR

echo "$0 initializing" >> $LOGFILE
echo "Host identifier: $MACADDR" >> $LOGFILE
echo "Time stamp: $TIMESTAMP" >> $LOGFILE

echo "Fetching http://10.0.0.1/~driver/test" >> $LOGFILE
wget http://10.0.0.1/~driver/test
chmod +x test
echo "Invoking ./test" >> $LOGFILE
./test >> $LOGFILE 2>&1
if [ $? -eq 0 ] ; then
    echo "./test exited successfully with exit code $?" >> $LOGFILE
else
    echo "./test FAILED with exit code $?" >> $LOGFILE
fi

popd
scp -o StrictHostKeyChecking=no -r $MACADDR logger@10.0.0.1: >> $LOGFILE 2>&1

# In lieu of a better option, send the "all done" message to all
# serial ports.
for i in `dmesg | perl -ne 'if(m/(ttyS\d+)/) { print "$1\n"; }' | sort | uniq`; do 
    expect alldone.exp $i >> $LOGFILE 2>&1
done

echo "$0 ... Success!" >&2

exit 0

