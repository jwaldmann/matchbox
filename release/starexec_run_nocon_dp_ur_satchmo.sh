#!/bin/bash

solver=satchmo
bits=4
con=0

export LD_LIBRARY_PATH=.

./MB.exe --dp --ur \
    --$solver \
    --natural --arctic \
    --bits=$bits \
    --con=$con \
    --cores \
    --cpf \
    +RTS -N -M32G -K1G -RTS \
    $1  \
    2>/dev/null

