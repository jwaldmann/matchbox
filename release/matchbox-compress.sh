#!/bin/bash

bits=5
dim=5

export LD_LIBRARY_PATH=.

./MB.exe --cpf \
    --dim=$dim --bits=$bits \
    --parallel --dp-fromtop -C --mirror \
    +RTS -N -M32G -K1G -RTS \
    $1

