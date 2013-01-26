#!/bin/bash

bits=6
dim=6

./matchbox-compress.bin \
    --dim=$dim --bits=$bits \
    --parallel --dp --compression-weak \
    +RTS -N -M32G -K1G -RTS \
    $1

