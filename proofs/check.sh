#!/bin/sh
set -eu
cd $(dirname $0)

echo "-R src SF" >_CoqProject
find src | grep ".v$" >>_CoqProject
coq_makefile -f _CoqProject -o Makefile
make
