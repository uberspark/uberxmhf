#!/usr/bin/python -u
# -u     Force  stdin, stdout and stderr to be totally unbuffered. 

import sys, json, base64, binascii, os, subprocess

#####################################################################
# We expect a single line of ASCII input which is JSON containing two
# base64-encoded nonces named tpm_nonce and utpm_nonce
#####################################################################
input = sys.stdin.readline()


print >> sys.stderr, "attestor.py read ("+input.rstrip()+")\n";

noncesdict = json.JSONDecoder().decode(input)['challenge']
tpm_nonce_b64 = noncesdict['tpm_nonce']
utpm_nonce_b64 = noncesdict['utpm_nonce']

print >> sys.stderr, "attestor.py decoded input:", noncesdict
print >> sys.stderr, "attestor.py decoded input:", tpm_nonce_b64
print >> sys.stderr, "attestor.py decoded input:", utpm_nonce_b64

# Decode base64 encoding to binary and prepare to print as ASCII hex 
tpm_nonce_ascii = binascii.hexlify(binascii.a2b_base64(tpm_nonce_b64))
print >> sys.stderr, "tpm_nonce_ascii",tpm_nonce_ascii

# Read one 16-byte UUID from /dev/urandom
urand = open('/dev/urandom', 'rb')
aik_uuid_ascii = binascii.hexlify(urand.read(16))
urand.close()

print >> sys.stderr, "aik_uuid_ascii", aik_uuid_ascii

### WARNING: This is currently extremely vulnerable to shell characters!
### TODO: regex to verify nothing but [0-9a-f]
#tpm_createkey_exec = "tpm_createkey -N -u "+aik_uuid_ascii+" -B "+aik_uuid_ascii+".keyfile\n"
tpm_createkey_exec = "echo Hello"
print >> sys.stderr, "Subprocess: "+tpm_createkey_exec

try:
    print >>sys.stderr, "Still here 1"
    retcode = subprocess.check_call(tpm_createkey_exec, shell=True)
    print >>sys.stderr, "Still here 2"
    if retcode < 0:
        print >>sys.stderr, "Child was terminated by signal", -retcode
    else:
        print >>sys.stderr, "Child returned", retcode
except OSError, e:
    print >>sys.stderr, "Execution failed:", e

print >>sys.stderr, "Still here 3"


# Using -B to write / read keyfile because LoadKeyByUUID fails otherwise
# I think this is a latent trousers or TPM bug

#tpm_createkey -N -u $UUID -B $UUID.keyfile
#tpm_quote -N -B $UUID.keyfile -u $UUID -n $NONCE -p 17 -p 18 -p 19



### Temporarily placate verifier.py since it expects some kind of response.
print "attestor.py read ("+input.rstrip()+") and has printed it!\n";
