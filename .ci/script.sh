#!/bin/bash

set -e

eval $(opam config env)
export Z3=z3-4.5.0-x64-ubuntu-14.04;
export PATH=/home/travis/build/mitls/hacl-star/$Z3/bin:$PATH;
export PATH=/home/travis/build/mitls/hacl-star:$PATH;
export PATH=/home/travis/build/mitls/hacl-star/dependencies/FStar/bin:$PATH;
export PATH=/home/travis/build/mitls/hacl-star/dependencies/kremlin:$PATH;
export KREMLIN_HOME=/home/travis/build/mitls/hacl-star/dependencies/kremlin
export FSTAR_HOME=/home/travis/build/mitls/hacl-star/dependencies/FStar

echo "\"$Z3\": -traverse" >> _tags
echo "\"$CLANG\": -traverse" >> _tags
echo "\"FStar\": -traverse" >> _tags
echo "\"kremlin\": -traverse" >> _tags

echo -e "\e[31m=== No Travis build necessary for NSS ===\e[0m"
