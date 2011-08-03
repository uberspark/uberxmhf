#!/usr/bin/python -u
# -u     Force  stdin, stdout and stderr to be totally unbuffered. 

import sys, json, base64

input = sys.stdin.readline()

print "attestor.py read ("+input.rstrip()+") and has printed it!\n";

