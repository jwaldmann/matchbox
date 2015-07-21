#!/bin/bash

export LD_LIBRARY_PATH=.

./MB.exe  \
    --cycle \
    --noh \
    +RTS -M7G -K1G -RTS \
    $1  \
    2>/dev/null

