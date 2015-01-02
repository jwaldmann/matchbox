#!/bin/bash

solver=satchmo
domain=arctic
encoding=plain
bits=8

export LD_LIBRARY_PATH=.

./MB.exe --cpf \
    --$solver \
    --$domain \
    --$encoding \
    --bits=$bits \
    +RTS -N -M32G -K1G -RTS \
    $1 \
    2>/dev/null
