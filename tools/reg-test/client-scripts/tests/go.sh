#!/bin/bash

BASEDIR=$(dirname $0)
LOGFILE=shell.log

echo "$0 initializing" >&2

MACADDR=$(./getmacaddr.sh)
# Disable local timestamp generation; get it from ISCSI_INITIATOR
#TIMESTAMP=$(./gettimestamp.sh)

# Typical values for ISCSI_INITIATOR look like this:
# iqn.78acc0b183aa.2012-02-16-14:37:32
# We want to strip off the timestamp at the end.
TIMESTAMP=`perl -ne 'if(m/ISCSI_INITIATOR=iqn\.[0-9a-f]+\.([0-9:-]+) /) { print "$1\n"; }' < /proc/cmdline`

# Sanity check the timestamp; if it's too short, don't use it. Should
# be 14 actual characters plus some punctuation, so compare against
# 14.
if [ ${#TIMESTAMP} -lt 14 ]; then
    TIMESTAMP="parse_error"
fi

TESTDIR=$MACADDR/$TIMESTAMP
mkdir -p $TESTDIR
pushd $TESTDIR

echo "$0 initializing" >> $LOGFILE
echo "Host identifier: $MACADDR" >> $LOGFILE
echo "Time stamp: $TIMESTAMP" >> $LOGFILE
echo "Environment:" >> $LOGFILE
set >> $LOGFILE

echo "Fetching http://10.0.0.1/~driver/test" >> $LOGFILE
wget http://10.0.0.1/~driver/test
chmod +x test
echo "Invoking ./test" >> $LOGFILE
for i in `seq 1 1`; do
    ./test >> $LOGFILE 2>&1
    if [ $? -eq 0 ] ; then
        echo "./test iteration $i exited successfully with exit code $?" >> $LOGFILE
    else
        echo "./test iteration $i FAILED with exit code $?" >> $LOGFILE
    fi
done

popd
scp -o StrictHostKeyChecking=no $TESTDIR/* logger@10.0.0.1:/var/www/logger/$TESTDIR >> $LOGFILE 2>&1

# In lieu of a better option, send the "all done" message to all
# serial ports.
for i in `dmesg | perl -ne 'if(m/(ttyS\d+)/) { print "$1\n"; }' | sort | uniq`; do 
    expect alldone.exp $i >> $LOGFILE 2>&1
done

echo "$0 ... Success!" >&2

exit 0

