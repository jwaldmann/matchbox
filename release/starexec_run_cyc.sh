#!/bin/bash

solver=satchmo
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
    +RTS -C -N -M7G -K1G -RTS \
    $1  \
    2>/dev/null

