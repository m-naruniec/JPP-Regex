#!/bin/bash

for ((i=0; i < $1; i++))
do
    echo "Iteration number: $i"
    time stack runhaskell ./TestReg.hs
done
