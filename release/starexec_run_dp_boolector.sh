#!/bin/bash

solver=boolector
bits=4
con=2

export LD_LIBRARY_PATH=.

./MB.exe --dp \
    --$solver \
    --natural \
    --bits=$bits \
    --con=$con --small \
    --cores \
    +RTS -N -M32G -K1G -RTS \
    $1  \
    2>/dev/null

