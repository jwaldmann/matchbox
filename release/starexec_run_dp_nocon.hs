#!/bin/bash

solver=satchmo
bits=4
con=0

export LD_LIBRARY_PATH=.

./MB.exe --dp \
    --$solver \
    --natural --arctic \
    --bits=$bits \
    --con=$con \
    +RTS -N -M32G -K1G -RTS \
    $1  \
    2>/dev/null

