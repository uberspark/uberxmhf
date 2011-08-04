#!/usr/bin/env python

import socket
import struct

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

def gen_audit_token(audit_nonce, audit_string):
    return "audit token!"

def send_audit_token(conn, audit_token):
    l = struct.pack("!I", len(audit_token))
    conn.send(l)
    conn.send(audit_token)
    return

def main():
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind((HOST, PORT))
    s.listen(1)
    while True:
        conn, addr = s.accept()
        print 'connected by', addr

        audit_nonce = read_audit_nonce(conn)
        audit_string = read_audit_string(conn)
        print "got " + audit_nonce + ", " + audit_string
        audit_token = gen_audit_token(audit_nonce, audit_string)
        send_audit_token(conn, audit_token)

if __name__ == '__main__':
    main()
