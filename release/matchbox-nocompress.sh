#!/bin/bash

bits=6
dim=6

export LD_LIBRARY_PATH=.

./MB.exe --cpf \
    --dim=$dim --bits=$bits \
    --parallel --dp-fromtop --mirror \
    +RTS -N -M32G -K1G -RTS \
    $1

