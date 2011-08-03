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

#print >> sys.stderr, "verifier.py got response (" + response.rstrip() + ")\n"

response_dict = json.JSONDecoder().decode(response)

#print >> sys.stderr, "response_dict:\n", response_dict
#print >> sys.stderr, "response:\n", response_dict["response"]
#print >> sys.stderr, "tpm_part:\n", response_dict["tpm_part"]
#print >> sys.stderr, "pal_part:\n", response_dict["pal_part"]


#####################################################################
# First make sure this is the expected "response" message
#####################################################################
if(response_dict["response"] != "tpm_and_utpm"):
    print >> sys.stderr, "ERROR:",response_dict["response"]," != \"tpm_and_utpm\""
    sys.exit(1)

#####################################################################
# Next parse out the TPM-based attestation:
# pcr17, pcr18, pcr19, sig, pubkey
#####################################################################
# NOTE: array-like access to a dict (a[k]) "Raises a KeyError
# exception if k is not in the map", so error-checking is implicit.
tpm_output_dict = response_dict["tpm_part"]
tpm_pcr17  = base64.b64decode(tpm_output_dict["pcr17"])
tpm_pcr18  = base64.b64decode(tpm_output_dict["pcr18"])
tpm_pcr19  = base64.b64decode(tpm_output_dict["pcr19"])
tpm_sig    = base64.b64decode(tpm_output_dict["sig"])
tpm_pubkey = base64.b64decode(tpm_output_dict["pubkey"])

#####################################################################
# Next parse out the uTPM-based attestation from the PAL
#####################################################################
pal_output_dict = response_dict["pal_part"]
pal_TopLevelTitle = pal_output_dict["TopLevelTitle"] # TODO: kill me
pal_DataStructureVersion = pal_output_dict["DataStructureVersion"] # TODO: kill me
pal_externalnonce     = base64.b64decode(pal_output_dict["externalnonce"])
pal_rsaMod            = base64.b64decode(pal_output_dict["rsaMod"])
pal_tpm_pcr_composite = base64.b64decode(pal_output_dict["tpm_pcr_composite"])
pal_sig               = base64.b64decode(pal_output_dict["sig"])


#

