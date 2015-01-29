#!/bin/bash

solver=boolector
domain=natural
bits=4
con=2

export LD_LIBRARY_PATH=.

./MB.exe --dp --ur \
    --$solver \
    --$domain \
    --bits=$bits \
    --con=$con \
    +RTS -N -M32G -K1G -RTS \
    $1  \
    2>/dev/null

