#!/bin/bash

###
#
# Master control script for nightly build and regression
# testing. Should cope if run as user 'driver' and not as root, but
# does employ sudo to elevate privileges to copy to test /boot
# partitions.
#
# Not doing "set -e" because this is the top-level script for
# unattended testing; it needs to cope with its own errors.
#
###

# This function takes one parameter: the full path of a logfile.
# That file is then augmented with some additional information,
# URLs are constructed, and an email is sent out announcing the
# completion of testing.
function email_logs () {
  STATUS_REPORT_FILE=/tmp/test-email.txt
  WEB_URL_BASE='emperor.pdl.cmu.local:8080'
  echo -e "Primary nightly build and test administration log:\n" > $STATUS_REPORT_FILE
  if [ -z $1 ]; then
      echo "ERROR: Function email_logs invoked without a log to email!" >> $STATUS_REPORT_FILE
  else
      echo $1 >> $STATUS_REPORT_FILE
  fi
  echo -e "\n\nIndividual test host results:\n" >> $STATUS_REPORT_FILE
  for i in `find /var/www/logger -type l`; do 
      find $i/ -name "*$TIMESTAMP*"; 
  done >> $STATUS_REPORT_FILE
  SUBJECT="[reg-test] squid test report for $TIMESTAMP"

  # Include convenient links in the email
  perl -pe "s/\/var\/www/http:\/\/$WEB_URL_BASE/" < $STATUS_REPORT_FILE | mailx -s "$SUBJECT" jonmccune@gmail.com jdnewsome@gmail.com amitvasudevan@gmail.com
}

## 0. Basic Setup

# Find the absolute path of this script and cd there.
MY_PATH=`dirname "$0"`
MY_PATH=`( cd "$MY_PATH" && pwd )`
cd $MY_PATH

LOGDIR_ROOT=/var/www/logger
export TIMESTAMP=`date --rfc-3339=seconds | tr ' ' - | cut -d - -f 1,2,3,4`
BUILD_LOG=$LOGDIR_ROOT/nightly-$TIMESTAMP.log

echo -e "\n$0: BEGINNING REGRESSION TEST SET WITH TIMESTAMP $TIMESTAMP\n" | tee -a $BUILD_LOG
echo "Environment:" >> $BUILD_LOG
set >> $BUILD_LOG
echo "" >> $BUILD_LOG

## Make sure the current user is in groups logger and dialout
if [ `groups | grep logger | grep dialout | wc -l` -lt 1 ]; then
    echo -e "\nERROR: CURRENT USER NOT IN GROUPS logger, dialout!!!\n" >> $BUILD_LOG
    email_logs $BUILD_LOG
    exit 1
fi

## 1. Build everything

echo -e "\nSTARTING EXHAUSTIVE BUILD\n" | tee -a $BUILD_LOG
bash build-tv.sh >> $BUILD_LOG 2>&1
rc=$?
if [[ $rc != 0 ]] ; then
    echo -e "\nERROR: BUILD FAILED; ABORTING REMAINING REGRESSION TESTING!!!\n" >> $BUILD_LOG
    email_logs $BUILD_LOG
    exit $rc
fi

## 2. Copy the hypervisor files to all the test hosts' /boot's

# TODO: Centralize all path settings
EMHF_RELPATH=../../../xmhf
if [ ! -d "$EMHF_RELPATH" ]; then
    echo -e "\nERROR: EMHF_RELPATH $EMHF_RELPATH DOES NOT EXIST; ABORTING REMAINING REGRESSION TESTING!!!\n" >> $BUILD_LOG
    email_logs $BUILD_LOG
    exit 1
fi

# TODO: Perhaps somehow stop requiring 'driver' to be a no-password
# sudoer. Ugh.
sudo -n true
rc=$?
if [[ $rc != 0 ]] ; then
    echo -e "\nERROR: CANNOT sudo FOR ./copy_to_slashboots.sh; ABORTING REMAINING REGRESSION TESTING!!!\n" >> $BUILD_LOG
    email_logs $BUILD_LOG
    exit $rc
fi

sudo bash copy_to_slashboots.sh $EMHF_RELPATH/init-x86.bin $EMHF_RELPATH/hypervisor-x86.bin.gz >> $BUILD_LOG 2>&1
rc=$?
if [[ $rc != 0 ]] ; then
    echo -e "\nERROR: ./copy_to_slashboots.sh FAILED; ABORTING REMAINING REGRESSION TESTING!!!\n" >> $BUILD_LOG
    email_logs $BUILD_LOG
    exit $rc
fi

## 3. Create a tests.tgz tarball

CLI_SCR_PATH=../client-scripts
if [ ! -d $CLI_SCR_PATH ]; then
    echo -e "\nERROR: DIRECTORY $CLI_SCR_PATH DOES NOT EXIST; ABORTING REMAINING REGRESSION TESTING!!!\n" >> $BUILD_LOG
    email_logs $BUILD_LOG
    exit $rc
fi

pushd $CLI_SCR_PATH
bash make-tarball.sh >> $BUILD_LOG 2>&1
cp -av tests.tgz /home/driver/public_html >> $BUILD_LOG 2>&1
popd


## 4. Copy test PAL into place
## TODO: Get more PALs!!!
## TODO: Bundle PALs into tests.tgz
TEST_PAL_PATH=../../../tee-sdk/examples/test/test
if [ ! -e $TEST_PAL_PATH ]; then
    echo -e "\nERROR: TEST PAL $TEST_PAL_PATH DOES NOT EXIST; ABORTING REMAINING REGRESSION TESTING!!!\n" >> $BUILD_LOG
    email_logs $BUILD_LOG
    exit $rc
fi
cp -av $TEST_PAL_PATH /home/driver/public_html >> $BUILD_LOG 2>&1

## 5. Invoke the tests on all of the test hosts
## Note: sequence-tests.sh is responsible for its own logging;
## we only grab stderr here.
echo -e "\nBEGINNING sequence-tests.sh\n" >> $BUILD_LOG
/usr/bin/time -o time.log -a ./sequence-tests.sh 2>> $BUILD_LOG
rc=$?
if [[ $rc != 0 ]] ; then
    echo -e "\nERROR: sequence-tests.sh FAILED!!!\n" >> $BUILD_LOG
    email_logs $BUILD_LOG
    exit $rc
fi
cat time.log >> $BUILD_LOG
rm time.log
echo -e "\nCOMPLETED sequence-tests.sh\n" >> $BUILD_LOG

echo -e "\nCOMPLETED $0; SUCCESS!!!\n" | tee -a $BUILD_LOG

## 6. Send an email announcing new test results are available
email_logs $BUILD_LOG

