#!/usr/bin/python -u
# -u     Force  stdin, stdout and stderr to be totally unbuffered. 

import sys, json, base64, binascii, os, subprocess, signal, re

#####################################################################
# We expect a single line of ASCII input which is JSON containing two
# base64-encoded nonces named tpm_nonce and utpm_nonce
#####################################################################
input = sys.stdin.readline()

#print >>sys.stderr, "attestor.py read ("+input.rstrip()+")\n";
noncesdict = json.JSONDecoder().decode(input)['challenge']
tpm_nonce_b64 = noncesdict['tpm_nonce']
utpm_nonce_b64 = noncesdict['utpm_nonce']

print >>sys.stderr, "attestor.py decoded input:", noncesdict
#print >>sys.stderr, "attestor.py decoded input:", tpm_nonce_b64
#print >>sys.stderr, "attestor.py decoded input:", utpm_nonce_b64

# Decode base64 encoding to binary and prepare to reformat as ASCII hex 
tpm_nonce_ascii = binascii.hexlify(binascii.a2b_base64(tpm_nonce_b64))
utpm_nonce_ascii = binascii.hexlify(binascii.a2b_base64(utpm_nonce_b64))
#print >>sys.stderr, "tpm_nonce_ascii",tpm_nonce_ascii

#####################################################################
# Before generating any quotes, we must have an AIK to use to sign
# the hardware TPM's quote.  We create a new one here using
# tpm_createkey from OpenPTS.  This is suboptimal, not the least
# because of the LoadKeyByUUID bug mentioned below. Really we should
# check for an existing AIK and use it if found, instead of creating
# a new one every time.
#####################################################################

# Read one 16-byte UUID from /dev/urandom
urand = open('/dev/urandom', 'rb')
aik_uuid_ascii = binascii.hexlify(urand.read(16))
urand.close()

#print >>sys.stderr, "aik_uuid_ascii", aik_uuid_ascii

# Being conservative and ensuring no shell escapes, even though this comes straight from hexlify()
filter = re.compile("[^0-9a-fA-F]")
if filter.search(aik_uuid_ascii) != None:
    print >>sys.stderr, "ERROR: aik_uuid_ascii contains ILLEGAL characters:", aik_uuid_ascii
    sys.exit(1)
if filter.search(tpm_nonce_ascii) != None:
    print >>sys.stderr, "ERROR: tpm_nonce_ascii contains ILLEGAL characters:", tpm_nonce_ascii
    sys.exit(1)
if filter.search(utpm_nonce_ascii) != None:
    print >>sys.stderr, "ERROR: utpm_nonce_ascii contains ILLEGAL characters:", utpm_nonce_ascii
    sys.exit(1)
# Using -B to write / read keyfile because LoadKeyByUUID fails otherwise.
# I think this is a latent trousers or TPM bug.
# TODO: work-around by breaking dependence on OpenPTS
tpm_createkey_exec = "tpm_createkey -N -u "+aik_uuid_ascii+" -B "+aik_uuid_ascii+".keyfile\n"
print >>sys.stderr, "Subprocess: "+tpm_createkey_exec

# If run in an environment where SIGCHLD is explicitly set to SIG_IGN, wait() will trigger an ECHILD exception.
# See 'man wait' for details.  We avoid this by explicitly resetting SIGCHLD to the default signal handler.
signal.signal(signal.SIGCHLD, signal.SIG_DFL)
try:
    proc = subprocess.Popen(tpm_createkey_exec, bufsize=0, shell=True, stderr=subprocess.PIPE, stdin=subprocess.PIPE, stdout=subprocess.PIPE, close_fds=True)
    proc.wait()
    stdout_value, stderr_value = proc.communicate()
    if proc.returncode != 0:
        print >>sys.stderr, "Child was terminated by signal", proc.returncode
        print >>sys.stderr, "Child stderr: ", stderr_value
        print >>sys.stderr, "Child stdout: ", stdout_value
        sys.exit(1)
    else:
        print >>sys.stderr, "Child completed successfully ( exit code", proc.returncode, ")"
except OSError, e:
    print >>sys.stderr, "Execution failed:", e
    sys.exit(1)



#####################################################################
# Now generate the actual TPM Quote covering PCRs 17, 18, and 19.
# 17: SINIT module on Intel systems, TrustVisor SL on AMD systems
# 18: TrustVisor SL on Intel systems, unused on AMD systems
# 19: TrustVisor runtime extends this with the public uTPM signing key
#
# Again we use a tool from OpenPTS.  Eventually we should build our
# own tools.
#####################################################################

#tpm_createkey -N -u $UUID -B $UUID.keyfile
tpm_quote_exec = "tpm_quote -N -B "+aik_uuid_ascii+".keyfile -u "+aik_uuid_ascii+" -n "+tpm_nonce_ascii+" -p 17 -p 18 -p 19"
print >>sys.stderr, "Subprocess: "+tpm_quote_exec
stdout_value = "" # want to keep this in scope beyond 'try' block
try:
    proc = subprocess.Popen(tpm_quote_exec, bufsize=0, shell=True, stderr=subprocess.PIPE, stdin=subprocess.PIPE, stdout=subprocess.PIPE, close_fds=True)
    proc.wait()
    stdout_value, stderr_value = proc.communicate()
    if proc.returncode != 0:
        print >>sys.stderr, "Child was terminated by signal", proc.returncode
        print >>sys.stderr, "Child stderr: ", stderr_value
        print >>sys.stderr, "Child stdout: ", stdout_value
        sys.exit(1)
    else:
        print >>sys.stderr, "Child completed successfully ( exit code", proc.returncode, ")"
        #print >>sys.stderr, "Child output:\n",stdout_value
except OSError, e:
    print >>sys.stderr, "Execution failed:", e
    sys.exit(1)


#####################################################################
# Now we must parse the output from tpm_quote
# We are interested in 5 lines, each one of which begins with (in 
# the given order):
# pcr.17=
# pcr.18=
# pcr.19=
# signature=
# pubkey=
#
# Multilne regex to grab everything in one go.  DOTALL lets . match
# newlines, ?P<> syntax names matches, and groupdict() builds python
# dict which is trivially convertible to JSON for returning. :)
#####################################################################
m = re.match(r".*pcr\.17=(?P<pcr17>[0-9a-fA-F]+)"+
             r".*pcr\.18=(?P<pcr18>[0-9a-fA-F]+)"+
             r".*pcr\.19=(?P<pcr19>[0-9a-fA-F]+)"+
             r".*quoteinfo=(?P<quoteinfo>[0-9a-fA-F]+)"+
             r".*signature=(?P<sig>[0-9a-fA-F]+)"+
             r".*pubkey=(?P<pubkey>[0-9a-fA-F]+)", 
             stdout_value, re.DOTALL)
tpm_output_dict = m.groupdict()
#print >>sys.stderr, "m:", tpm_output_dict

# Re-encode the ASCII hex as base64 (need to step through raw binary to get there)
for item in tpm_output_dict:
    tpm_output_dict[item] = binascii.b2a_base64(binascii.unhexlify(tpm_output_dict[item]))
    
### TODO: Ensure that pubkey actually goes with the key generated with
### tpm_createkey above, and get a real certificate for it.

#####################################################################
# Now we will actually invoke the PAL and grab the uTPM quote output
#####################################################################
pal_exec = "./attestation "+ utpm_nonce_ascii
print >>sys.stderr, "Subprocess: "+pal_exec
try:
    proc = subprocess.Popen(pal_exec, bufsize=0, shell=True, stderr=subprocess.PIPE, stdin=subprocess.PIPE, stdout=subprocess.PIPE, close_fds=True)
    proc.wait()
    stdout_value, stderr_value = proc.communicate()
    if proc.returncode != 0:
        print >>sys.stderr, "Child was terminated by signal", proc.returncode
        print >>sys.stderr, "Child stderr: ", stderr_value
        print >>sys.stderr, "Child stdout: ", stdout_value
        sys.exit(1)
    else:
        print >>sys.stderr, "Child completed successfully ( exit code", proc.returncode, ")"
        print >>sys.stderr, "Child output:\n",stderr_value
except OSError, e:
    print >>sys.stderr, "Execution failed:", e
    sys.exit(1)

# stdout from pal_exec should already look like JSON
pal_output_dict = json.JSONDecoder().decode(stdout_value)
#print >>sys.stderr, "pal_output_dict:\n", pal_output_dict


#####################################################################
# Now we will combine both the TPM quote output and PAL uTPM quote
# output and encode it all as one big JSON structure to send back to
# verifier.py
#####################################################################

combined_dict = {"response": "tpm_and_utpm"}
combined_dict["tpm_part"] = tpm_output_dict
combined_dict["pal_part"] = pal_output_dict
#print >>sys.stderr, "combined_dict:\n", combined_dict

combined_json = json.JSONEncoder().encode(combined_dict)
#print >>sys.stderr, "combined_json:\n", combined_json

### Send back the actual response
print combined_json
