#!/bin/bash

# Thanks: http://www.revsys.com/writings/quicktips/nat.html

echo 1 > /proc/sys/net/ipv4/ip_forward

/sbin/iptables -t nat -A POSTROUTING -o eth1 -j MASQUERADE
/sbin/iptables -A FORWARD -i eth1 -o eth0 -m state --state RELATED,ESTABLISHED -j ACCEPT
/sbin/iptables -A FORWARD -i eth0 -o eth1 -j ACCEPT

