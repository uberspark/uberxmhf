#!/bin/sh

export PATH=/sbin:/bin:/usr/bin:$PATH

/sbin/ifconfig \
  | grep eth0 \
  | tr -s ' ' \
  | cut -d ' ' -f 5 \
  | tr ':' '-'


