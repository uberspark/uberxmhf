#!/usr/bin/python -u
# -u     Force  stdin, stdout and stderr to be totally unbuffered. 

# System modules
import base64, binascii, hashlib, json, sys, M2Crypto
# Our own modules
import common

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
# NOTE: Array-like access to a dict (a[k]) "Raises a KeyError
# exception if k is not in the map."  Regarding b64decode, "A
# TypeError is raised if s were incorrectly padded or if there are
# non-alphabet characters present in the string."
# Therefore, we do have implicit error-checking here.
tpm_output_dict = response_dict["tpm_part"]
tpm_pcr17     = base64.b64decode(tpm_output_dict["pcr17"])
tpm_pcr18     = base64.b64decode(tpm_output_dict["pcr18"])
tpm_pcr19     = base64.b64decode(tpm_output_dict["pcr19"])
tpm_quoteinfo = base64.b64decode(tpm_output_dict["quoteinfo"])
tpm_sig       = base64.b64decode(tpm_output_dict["sig"])
tpm_pubkey    = base64.b64decode(tpm_output_dict["pubkey"])

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

#####################################################################
#####################################################################
###################### VERIFICATION BEGINS HERE #####################
#####################################################################
#####################################################################

#####################################################################
# Step 0: Check the AIK certificate 
# XXX TODO: implement Privacy CA
#####################################################################

#####################################################################
# Step 1a: Verify TPM Quote (tpm_sig) using public AIK (tpm_pubkey)
#####################################################################

#tpm_sig was produced when the TPM signed tpm_quoteinfo with
#tpm_pubkey's private counterpart

#print >>sys.stderr, "validate_aik_blob(tpm_pubkey):", common.validate_aik_blob(tpm_pubkey)

if common.validate_aik_blob(tpm_pubkey) != True:
    print >>sys.stderr, "ERROR: validate_aik_blob(tpm_pubkey) FAILED"
    sys.exit(1)

# Public key object used to verify the signature
rsa = common.aik_blob_to_m2rsa(tpm_pubkey)

# Hash the quoteinfo
digest = hashlib.sha1(tpm_quoteinfo).digest()
#print >>sys.stderr, "digest: ", binascii.hexlify(digest)

# Check the actual signature
if rsa.verify(digest, tpm_sig) != 1:
    print >>sys.stderr, "RSA signature verification of TPM Quote FAILED!"
    sys.exit(1)

#####################################################################
# Step 1b: Verify quoteinfo contains the right "magic" and the nonce
# we originally sent.
# 
# typedef struct tdTPM_QUOTE_INFO{
#   TPM_STRUCT_VER version;
#   BYTE fixed[4];
#   TPM_COMPOSITE_HASH digestValue;
#   TPM_NONCE externalData;
# }TPM_QUOTE_INFO;

#####################################################################
if(tpm_quoteinfo.find(binascii.unhexlify("0101000051554f54")) != 0):
    print >>sys.stderr, "ERROR: \"Quote Magic\" not found in TPM Quote_Info!!!"
    sys.exit(1)

if(tpm_quoteinfo.find(tpm_nonce_bytes) != 28):
    print >>sys.stderr, "ERROR: Nonce not found in TPM Quote_Info!!!"
    sys.exit(1)

#####################################################################
# Step 1c: Verify quoteinfo contains a digest of PCRs 17, 18, 19
#
# typedef struct tdTPM_PCR_SELECTION {
#   UINT16 sizeOfSelect;
#   [size_is(sizeOfSelect)] BYTE pcrSelect[];
# } TPM_PCR_SELECTION;
#
# typedef struct tdTPM_PCR_COMPOSITE {
#   TPM_PCR_SELECTION select;
#   UINT32 valueSize;
#   [size_is(valueSize)] TPM_PCRVALUE pcrValue[];
# } TPM_PCR_COMPOSITE;
#####################################################################

tpm_pcr_selection = binascii.unhexlify("000300000e")
valueSize = binascii.unhexlify("0000003c") # 3 PCRs = 3*0x14 = 0x3c
tpm_pcr_composite = tpm_pcr_selection + valueSize + tpm_pcr17 + tpm_pcr18 + tpm_pcr19
tpm_composite_hash = hashlib.sha1(tpm_pcr_composite).digest()

if tpm_quoteinfo.find(tpm_composite_hash) != 8:
    print >>sys.stderr, "ERROR: PCR values in tpm_composite_hash don't match tpm_quoteinfo"
    sys.exit(1)

#####################################################################
# Step 2: Verify that the PAL-provided public signing key was measured
# into PCR-19.
#
# PCR-19 = SHA-1 ( 0x00^20 | SHA-1 ( pal_rsaMod ) )
#####################################################################
pcr19_hash_payload = binascii.unhexlify("0000000000000000000000000000000000000000")
tv_serialized_rsa_prefix = binascii.unhexlify("0000010000010001") # len(N) | e
pcr19_hash_payload += hashlib.sha1(tv_serialized_rsa_prefix + pal_rsaMod).digest()
pcr19_computed_value = hashlib.sha1(pcr19_hash_payload).digest()

if(tpm_pcr19.find(pcr19_computed_value) != 0):
    print >>sys.stderr, "ERROR: PCR-19 does not match pal_rsaMod"
    print >>sys.stderr, "pcr-19:", binascii.hexlify(tpm_pcr19)
    print >>sys.stderr, "pal_rsaMod:", binascii.hexlify(pal_rsaMod)
    sys.exit(1)

print >>sys.stderr, "**************************************"
print >>sys.stderr, "****** VERIFICATION SUCCESSFUL! ******"
print >>sys.stderr, "**************************************"

#

