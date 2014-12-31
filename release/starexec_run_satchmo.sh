#!/bin/bash

solver=satchmo
domain=natural
bits=4

export LD_LIBRARY_PATH=.

./MB.exe --cpf \
    --$solver \
    --$domain \
    --bits=$bits \
    +RTS -N -M32G -K1G -RTS \
    $1  \
    2>/dev/null

