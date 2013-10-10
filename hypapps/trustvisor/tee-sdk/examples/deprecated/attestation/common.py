#!/usr/bin/python
# Filename: common.py

import binascii, sys, M2Crypto

def sayhi():
    print >>sys.stderr, "Hi, this is common.py speaking"

#####################################################################
# When a TPM exports a public key it is generally in an internal
# format defined as TPM_PUBKEY.  Nested inside are several other
# structures.  Here is a representative pubkey, followed by the C
# definitions of the relevant data structures.  The intention is to
# document where 'aik_prefix_magic' comes from, to make the key
# validation function comprehensible.
#####################################################################

aik_prefix_magic = binascii.unhexlify("00000001000100020000000c00000800000000020000000000000100")

# pubkey=00000001000100020000000c00000800000000020000000000000100869d3a1f6548e7d8b5b9f14b6b74ea4a0ab32f4d446915c33325d9cce0d466df03718c6b383d8069a94352d268b3ab99a4db92ba2c6b9dd78c554762f14ed6e07210569c47cce45d4d2f4741852fe0e4ebef1ef74ca78a1f1032ab0c39d8b57f47db3c603d6afae1609388cd667e2acb3d3805064488a2dc99f82d948d0d16b2f20517e76887375c5d76c18c9bd445ea0860e75b7f04d1db042c6608f42696e20ab7cffdb2f091dc373284b53c56922524224e25e92086f6923d78fe63956ad995a4915747550aae591a00cda9f829a24ae5aa8c8d16a84fe4619cb7a64dcd621b3f21cbe43b20fce269b860780ded53c9644cb849f3acec30b3e1944b742c4b

# typedef struct TPM_PUBKEY {
#   TPM_KEY_PARMS algorithmParms;
#   TPM_STORE_PUBKEY pubKey;
# } TPM_PUBKEY;

# typedef struct TPM_KEY_PARMS {
#   TPM_ALGORITHM_ID algorithmID;
#   TPM_ENC_SCHEME encScheme;
#   TPM_SIG_SCHEME sigScheme;
#   UINT32 parmSize;
#   BYTE* parms;
# } TPM_KEY_PARMS;

# typedef struct TPM_RSA_KEY_PARMS {  
#   UINT32 keyLength; 
#   UINT32 numPrimes; 
#   UINT32 exponentSize;
#   BYTE* exponent;
# } TPM_RSA_KEY_PARMS;

# typedef struct TPM_STORE_PUBKEY {
#   UINT32 keyLength;
#   BYTE* key;
# } TPM_STORE_PUBKEY;

### Now, taking apart the representative pubkey:

# pubkey=
# TPM_KEY_PARMS:
# 00000001 #define TPM_ALG_RSA 0x00000001 // TPM_ALGORITHM_ID values
# 0001 #define TPM_ES_NONE 0x0001 // TPM_ENC_SCHEME values
# 0002 #define TPM_SS_RSASSAPKCS1v15_SHA1 0x0002 // TPM_SIG_SCHEME values
# 0000000c   UINT32 parmSize; == 12
# //This SHALL be the parameter information dependant upon the key algorithm.
# TPM_RSA_KEY_PARMS:
# 00000800 keyLength = 2048 bits
# 00000002 numPrimes = 2
# 00000000 exponentSize = 0 ** we are only the public key
# TPM_STORE_PUBKEY:
# 00000100 (length = 256 bytes) 
# the actual key modulus:
# 869d3a1f6548e7d8b5b9f14b6b74ea4a0ab32f4d446915c33325d9cce0d466df03718c6b383d8069a94352d268b3ab99a4db92ba2c6b9dd78c554762f14ed6e07210569c47cce45d4d2f4741852fe0e4ebef1ef74ca78a1f1032ab0c39d8b57f47db3c603d6afae1609388cd667e2acb3d3805064488a2dc99f82d948d0d16b2f20517e76887375c5d76c18c9bd445ea0860e75b7f04d1db042c6608f42696e20ab7cffdb2f091dc373284b53c56922524224e25e92086f6923d78fe63956ad995a4915747550aae591a00cda9f829a24ae5aa8c8d16a84fe4619cb7a64dcd621b3f21cbe43b20fce269b860780ded53c9644cb849f3acec30b3e1944b742c4b


# Ensure that blob begins with aik_prefix_magic and that the remainder
# of the blob is the right length.
def validate_aik_blob(blob):
    # Make sure the right prefix magic is there
    if(blob.find(aik_prefix_magic) != 0):
        print >>sys.stderr, "aik_prefix_magic not found in blob"
        return False
    # validate the overall length of the blob
    if(len(blob)-len(aik_prefix_magic) != 256):
        print >>sys.stderr, "blob - aik_prefix_magic != 256!", len(blob)-len(aik_prefix_magic)
        return False
    return True


# Grab the RSA public key components out of the blob and return an
# initialized M2Crypto.RSA context.
def aik_blob_to_m2rsa(blob):
    n_bin = blob[len(aik_prefix_magic):]
    n = M2Crypto.m2.bn_to_mpi(M2Crypto.m2.bin_to_bn(n_bin))
    e = M2Crypto.m2.bn_to_mpi(M2Crypto.m2.hex_to_bn("10001"))
    #print >>sys.stderr, "e: ", binascii.hexlify(e)
    #print >>sys.stderr, "n: ", binascii.hexlify(n)
    rsa = M2Crypto.RSA.new_pub_key((e, n))
    return rsa

version = '0.1'

# End of common.py
