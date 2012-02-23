#!/bin/bash

set -e

echo -e "\$0: nPREPARING TO CREATE tests.tgz\n"

tar czvf tests.tgz tests
cp tests.tgz /home/driver/public_html

echo -e "\n$0: tests.tgz COPIED TO public_html\n"
