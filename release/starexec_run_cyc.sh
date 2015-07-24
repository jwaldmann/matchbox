#!/bin/bash

solver=boolector
bits=4
con=0

export LD_LIBRARY_PATH=.

./MB.exe  \
    --cycle \
    --$solver \
    --arctic --natural \
    --bits=$bits \
    --con=$con \
    --both \
    --cores \
    +RTS -N -M7G -K1G -RTS \
    $1  \
    2>/dev/null

