#!/bin/bash

set -e

#HOSTS="test-e8100 pratt test-6555b creeper"
HOSTS="caisson cowabunga pratt test-6555b creeper"

LOGDIR_ROOT=/var/www/logger

# If TIMESTAMP was already defined by a parent script, don't
# regenerate it.
if [ ${#TIMESTAMP} -lt 14 ]; then
    TIMESTAMP=`date --rfc-3339=seconds | tr ' ' - | cut -d - -f 1,2,3,4`
fi
echo "$0: Using TIMESTAMP $TIMESTAMP" 1>&2

for i in $HOSTS; do
    HOSTLOGDIR=$LOGDIR_ROOT/$i
    
    if [ ! -d $HOSTLOGDIR ]; then
        echo "FATAL ERROR: $LOGDIR does not exist!"
        exit 1
    fi

    THISLOGDIR=$HOSTLOGDIR/$TIMESTAMP
    mkdir -m 2775 $THISLOGDIR
    LOGFILE=$THISLOGDIR/boot-test.log

    echo -e "#############################################"\
            "\n### STARTING tests on Host $i"\
            "\n### Log directory: $THISLOGDIR"\
            "\n### Timestamp:     $TIMESTAMP\n\n"\
        | tee -a $LOGFILE

    # bash has a built-in time command; we don't want to use it.
    /usr/bin/time -o /tmp/time-$i.log ./boot-test.sh $i 2>&1 | tee -a $LOGFILE
    cat /tmp/time-$i.log | tee -a $LOGFILE

    echo -e "##############################################"\
            "\n### COMPLETED tests on Host $i"\
            "\n##############################################\n\n"\
        | tee -a $THISLOGDIR/boot-test.log
#    sleep 1
done
