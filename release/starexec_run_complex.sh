#!/bin/bash

solver=satchmo
domain=natural
bits=4
con=1

export LD_LIBRARY_PATH=.

./MB.exe  \
    --complexity \
    --$solver \
    --$domain \
    --bits=$bits \
    --con=$con \
    +RTS -N -M32G -K1G -RTS \
    $1  \
    2>/dev/null

