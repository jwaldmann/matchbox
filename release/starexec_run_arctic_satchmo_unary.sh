#!/bin/bash

solver=satchmo
domain=arctic
bits=8

export LD_LIBRARY_PATH=.

./MB.exe --cpf \
    --$solver \
    --$domain \
    --unary \
    --bits=$bits \
    +RTS -N -M32G -K1G -RTS \
    $1 \
    2>/dev/null


