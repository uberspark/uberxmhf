#!/usr/bin/python -u
# -u     Force  stdin, stdout and stderr to be totally unbuffered. 

import sys, json, base64

# Read two 20-byte nonces from /dev/urandom
urand = open('/dev/urandom', 'rb')
utpm_nonce_bytes = urand.read(20)
tpm_nonce_bytes = urand.read(20)
urand.close()

#print >> sys.stderr, "utpm_nonce b64:", base64.b64encode(utpm_nonce_bytes)
#print >> sys.stderr, "tpm_nonce  b64:", base64.b64encode(tpm_nonce_bytes)

utpm_dict = {"utpm_nonce": base64.b64encode(utpm_nonce_bytes), "tpm_nonce": base64.b64encode(tpm_nonce_bytes)}

print json.JSONEncoder().encode({"challenge": utpm_dict})

response = sys.stdin.readline()

print >> sys.stderr, "verifier.py got response (" + response.rstrip() + ")\n"
