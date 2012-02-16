#!/bin/bash

HOSTS="test-e8100 pratt test-6555b creeper"

LOGDIR_ROOT=/home/logger/public_html

for i in $HOSTS; do
    export TIMESTAMP=`date --rfc-3339=seconds | tr ' ' - | cut -d - -f 1,2,3,4`
    HOSTLOGDIR=$LOGDIR_ROOT/$i
    
    if [ ! -d $HOSTLOGDIR ]; then
        echo "FATAL ERROR: $LOGDIR does not exist!"
        exit
    fi

    THISLOGDIR=$HOSTLOGDIR/$TIMESTAMP
    mkdir -p $THISLOGDIR
    chown logger:logger $THISLOGDIR
    LOGFILE=$THISLOGDIR/boot-test.log

    echo -e "#############################################\n"\
            "########## STARTING tests on Host $i \n"\
            "#############################################\n"\
            "### Log directory: $THISLOGDIR\n"\
            "### TIMESTAMP:     $TIMESTAMP\n\n"\
        | tee -a $LOGFILE

    # bash has a built-in time command; we don't want to use it.
    /usr/bin/time -o /tmp/time.log ./boot-test.sh $i 2>&1 | tee -a $LOGFILE
    cat /tmp/time.log | tee -a $LOGFILE

    echo -e "##############################################\n"\
            "########## COMPLETED tests on Host $i \n"\
            "##############################################\n\n"\
        | tee -a $THISLOGDIR/boot-test.log
    sleep 1
done
