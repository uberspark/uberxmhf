#!/usr/bin/python -u
# -u     Force  stdin, stdout and stderr to be totally unbuffered. 

# System modules
import base64, binascii, hashlib, json, sys, M2Crypto
# Our own modules
import common

# Need to convert to PEM for m2crypto
# XXX currently unused, but will be when\if the pubkey format
# is compatible with m2crypto
def der2pem(der):
    TEMPLATE = """-----BEGIN PUBLIC KEY-----
%s
-----END PUBLIC KEY-----
"""
    rsa_pem = TEMPLATE % base64.encodestring(der).rstrip()
    return rsa_pem

# convert a long integer to m2crypto mpi
def long_to_mpi(x):
    h = hex(x)[2:].rstrip('L')
    return M2Crypto.m2.bn_to_mpi(M2Crypto.m2.hex_to_bn(h))

# Read two 20-byte nonces from /dev/urandom
urand = open('/dev/urandom', 'rb')
utpm_nonce_bytes = urand.read(20)
tpm_nonce_bytes = urand.read(20)
urand.close()

#print >>sys.stderr, "utpm_nonce b64:", base64.b64encode(utpm_nonce_bytes)
#print >>sys.stderr, "tpm_nonce  b64:", base64.b64encode(tpm_nonce_bytes)

utpm_dict = {"utpm_nonce": base64.b64encode(utpm_nonce_bytes), "tpm_nonce": base64.b64encode(tpm_nonce_bytes)}

print json.JSONEncoder().encode({"challenge": utpm_dict})

response = sys.stdin.readline()
print >>sys.stderr, "verifier.py got response (" + response.rstrip() + ")\n"

response_dict = json.JSONDecoder().decode(response)

#print >>sys.stderr, "response_dict:\n", response_dict
#print >>sys.stderr, "response:\n", response_dict["response"]
#print >>sys.stderr, "tpm_part:\n", response_dict["tpm_part"]
#print >>sys.stderr, "pal_part:\n", response_dict["pal_part"]


#####################################################################
# First make sure this is the expected "response" message
#####################################################################
if(response_dict["response"] != "tpm_and_utpm"):
    print >>sys.stderr, "ERROR:",response_dict["response"]," != \"tpm_and_utpm\""
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
pal_rsaPub            = base64.b64decode(pal_output_dict["rsaPub"])
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

print >>sys.stderr, "Step 0: Check the AIK certificate "
print >>sys.stderr, " XXX UNIMPLEMENTED XXX"

#####################################################################
# Step 1a: Verify TPM Quote (tpm_sig) using public AIK (tpm_pubkey)
#####################################################################

print >>sys.stderr, "Step 1a: Verifying TPM Quote RSA signature using public AIK "

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

print >>sys.stderr, "Step 1b: Verifying QuoteInfo contains the right magic and our nonce"

quote_magic8 = binascii.unhexlify("0101000051554f54")
if(tpm_quoteinfo.find(quote_magic8) != 0):
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

print >>sys.stderr, "Step 1c: Verifying QuoteInfo contains a digest of PCRs 17, 18, 19"

tpm_pcr_selection = binascii.unhexlify("000300000e")
valueSize = binascii.unhexlify("0000003c") # 3 PCRs = 3*0x14 = 0x3c
tpm_pcr_composite = tpm_pcr_selection + valueSize + tpm_pcr17 + tpm_pcr18 + tpm_pcr19
tpm_composite_hash = hashlib.sha1(tpm_pcr_composite).digest()

if tpm_quoteinfo.find(tpm_composite_hash) != 8:
    print >>sys.stderr, "ERROR: PCR values in tpm_composite_hash don't match tpm_quoteinfo"
    sys.exit(1)

#####################################################################
# Step 2: Verify that the PAL-provided public signing key was 
# measured into PCR-19.
#
# PCR-19 = SHA-1 ( 0x00^20 | SHA-1 ( len(N) | E | pal_rsaMod ) )
#####################################################################

print >>sys.stderr, "Step 2: Verifying TrustVisor pubkey is measured into HW TPM PCR-19"

pcr19_hash_payload = binascii.unhexlify("0000000000000000000000000000000000000000")
pcr19_hash_payload += hashlib.sha1( pal_rsaPub).digest()
pcr19_computed_value = hashlib.sha1( pcr19_hash_payload).digest()

if(tpm_pcr19.find(pcr19_computed_value) != 0):
    print >>sys.stderr, "ERROR: PCR-19 does not match pal_rsaMod"
    print >>sys.stderr, "pcr-19:", binascii.hexlify(tpm_pcr19)
    print >>sys.stderr, "pal_rsaPub:", binascii.hexlify(pal_rsaPub)
    sys.exit(1)

print >>sys.stderr, "  Verifying PCRs 17, 18 represent a known-good launch of TrustVisor"
print >>sys.stderr, "  XXX UNIMPLEMENTED XXX"

#####################################################################
# Step 3a: Check the uTPM RSA signature 
#
# Step 3b: Verify quoteinfo contains the right "magic" is implicit
# because we assemble the actual quoteinfo data structure from the
# provided pal_tpm_pcr_composite
#####################################################################

print >>sys.stderr, "Step 3a: Verifying uTPM Quote RSA signature with TrustVisor pubkey"

# reconstruct rsa pubkey
from pyasn1.codec.der import decoder as der_decoder
pal_rsaPub_decoder = der_decoder.decode( pal_rsaPub)
n = pal_rsaPub_decoder[0].getComponentByPosition(0)._value
e = pal_rsaPub_decoder[0].getComponentByPosition(1)._value
print >>sys.stderr, "e: ", hex(n)
print >>sys.stderr, "n: ", hex(e)
n = long_to_mpi(n)
e = long_to_mpi(e)
rsa = M2Crypto.RSA.new_pub_key((e, n))

# above block can be replaced with below when
# trustvisor encodes in SubjectPublicKeyInfo (which newest libtomcrypt does).
# (Or, when M2Crypto supports PKCS#1 RSAPublicKey. The underlying libcrypto
# supports it, but M2Crypto doesn't wrap that API.)
# pal_rsaPub_pem = der2pem(pal_rsaPub)
# print >>sys.stderr, "TrustVisor pubkey PEM:"
# print >>sys.stderr, pal_rsaPub_pem
# pal_rsaPub_pem_bio = M2Crypto.BIO.MemoryBuffer( pal_rsaPub_pem)
# rsa = M2Crypto.RSA.load_pub_key_bio(pal_rsaPub_pem_bio)

# Assemble PAL QuoteInfo
print >>sys.stderr, "Step 3b: Verifying uTPM QuoteInfo contains our nonce"

### Get rid of externalnonce; it's unnecessary
pal_quoteinfo = quote_magic8 + hashlib.sha1(pal_tpm_pcr_composite).digest() + utpm_nonce_bytes
pal_quoteinfo_digest = hashlib.sha1(pal_quoteinfo).digest()

#print >>sys.stderr, "PAL tpm_pcr_composite:", binascii.hexlify(pal_tpm_pcr_composite)
#print >>sys.stderr, "PAL quoteinfo:", binascii.hexlify(pal_quoteinfo)
#print >>sys.stderr, "PAL quoteinfo_digest:", binascii.hexlify(pal_quoteinfo_digest)

if rsa.verify(pal_quoteinfo_digest, pal_sig) != 1:
    print >>sys.stderr, "RSA signature verification of PAL's uTPM Quote FAILED!"
    sys.exit(1)

# pal_externalnonce     = base64.b64decode(pal_output_dict["externalnonce"])
# pal_rsaMod            = base64.b64decode(pal_output_dict["rsaMod"])
# pal_tpm_pcr_composite = base64.b64decode(pal_output_dict["tpm_pcr_composite"])
# pal_sig               = base64.b64decode(pal_output_dict["sig"])

#####################################################################
# Step 4: Confirm the right magic ASCII string is represented in uPCR0
#####################################################################

print >>sys.stderr, "  Verifying uPCR 0 represents a known-good launch of our PAL"
print >>sys.stderr, "  XXX UNIMPLEMENTED XXX"

print >>sys.stderr, "Step 4: Verifying data measured into uPCR 1 by PAL is represented in uTPM Quote"

pal_expected_input_data = "The quick brown fox jumped over the lazy dog!\0"
pal_expected_input_data_digest = hashlib.sha1(pal_expected_input_data).digest()
upcr1_hash_payload = binascii.unhexlify("0000000000000000000000000000000000000000") + pal_expected_input_data_digest
upcr1_computed = hashlib.sha1(upcr1_hash_payload).digest()
upcr1_extracted = pal_tpm_pcr_composite[27:] # tpm_pcr_selection(3) | valueSize(4) | uPcr0(20) | uPcr1(20)

if upcr1_extracted.find(upcr1_computed) != 0:
    print >>sys.stderr, "ERROR: upcr1_extracted != upcr1_computed"
    print >>sys.stderr, "    pal_tpm_pcr_composite", binascii.hexlify(pal_tpm_pcr_composite)
    print >>sys.stderr, "    upcr1_computed", binascii.hexlify(upcr1_computed)
    print >>sys.stderr, "    upcr1_extracted", binascii.hexlify(upcr1_extracted)
    sys.exit(1)

print >>sys.stderr, "**************************************"
print >>sys.stderr, "****** VERIFICATION SUCCESSFUL! ******"
print >>sys.stderr, "**************************************"

#

