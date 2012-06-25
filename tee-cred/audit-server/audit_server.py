#!/usr/bin/env python

import sys
import socket
import struct

from M2Crypto import RSA
import hashlib

PORT=9001
HOST=""

def recvall(conn, to_recv):
    recvd = 0
    chunks = []
    while recvd < to_recv:
        data = conn.recv(to_recv - recvd)
        recvd += len(data)
        chunks.append(data)
    return ''.join(chunks)

def read_audit_nonce(conn):
    l = struct.unpack("!I", conn.recv(4))[0]
    return recvall(conn, l)

def read_audit_string(conn):
    l = struct.unpack("!I", conn.recv(4))[0]
    return recvall(conn, l)

def gen_audit_token(privkey, audit_nonce, audit_string):
    h = hashlib.sha256()
    h.update(audit_nonce)
    h.update(audit_string)
    s = privkey.sign(h.digest(), algo='sha256')
    return s

def send_audit_token(conn, audit_token):
    l = struct.pack("!I", len(audit_token))
    conn.send(l)
    conn.send(audit_token)
    return

def main(privkey):
    import datetime
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind((HOST, PORT))
    s.listen(1)
    while True:
        conn, addr = s.accept()
        now = datetime.datetime.now()
        print now.__str__().split('.')[0]
        print '  From  : ', addr[0]

        audit_nonce = read_audit_nonce(conn)
        audit_string = read_audit_string(conn)
        # print "got " + audit_nonce.__repr__() + ", " + audit_string.__repr__()
        print "  Action: " + audit_string.__repr__()
        audit_token = gen_audit_token(privkey, audit_nonce, audit_string)

        # TEMP intentionally give invalid sig
        # audit_token = list(audit_token)
        # audit_token[-1] = chr(ord(audit_token[-1]) + 1)
        # audit_token = ''.join(audit_token)

        send_audit_token(conn, audit_token)

if __name__ == '__main__':
    privkey = RSA.load_key(sys.argv[1])
    main(privkey)
