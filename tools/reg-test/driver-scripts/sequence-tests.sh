#!/bin/bash

HOSTS="test-e8100 pratt test-6555b creeper"

LOGDIR_ROOT=/home/logger/public_html

for i in $HOSTS; do
    export TIMESTAMP=`date --rfc-3339=seconds | tr ' ' - | cut -d - -f 1,2,3,4`
    echo "################################################################################"
    echo "########## STARTING tests on Host $i ########"
    echo "################################################################################"
    HOSTLOGDIR=$LOGDIR_ROOT/$i
    
    if [ ! -d $HOSTLOGDIR ]; then
        echo "FATAL ERROR: $LOGDIR does not exist!"
        exit
    fi

    THISLOGDIR=$HOSTLOGDIR/$TIMESTAMP
    mkdir -p $THISLOGDIR
    chown logger:logger $THISLOGDIR
    echo "### Log directory: $THISLOGDIR"
    echo "### TIMESTAMP:     $TIMESTAMP"

    ./boot-test.sh $i 2>&1 | tee $THISLOGDIR/boot-test.log

    echo "################################################################################"
    echo "########## COMPLETED tests on Host $i ########"
    echo "################################################################################"
    echo ""
    sleep 1
done
