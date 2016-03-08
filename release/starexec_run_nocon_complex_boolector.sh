#!/bin/bash

solver=boolector
domain=natural
bits=4
con=0
pow=4

export LD_LIBRARY_PATH=.

./MB.exe  \
    --complexity --power-triangular=$pow \
    --$solver \
    --$domain \
    --bits=$bits \
    --con=$con \
    --cores \
    --latex \
    +RTS -N -M32G -K1G -RTS \
    $1  \
    2>/dev/null

