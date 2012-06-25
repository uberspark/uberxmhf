#!/bin/bash

socat exec:'python -u verifier.py' exec:'python -u attestor.py'

