#!/bin/bash

IDAPATH=${1:-/home/dario/ida-7.1/idat}
INDIR=${2:-/home/dario/phd/loaders_modeling/lang_parser/allcombo}
OUTDIR=${3:-/tmp/idaalldumps}

mkdir -p $OUTDIR

TESTCASES=$(ls $INDIR)
for f in $TESTCASES
do
    if [[ $f == *"cond"* ]]; then
	continue
    fi;
    ARG="idadumpmem.py $OUTDIR"
    $IDAPATH -A -B -c "-S$ARG" $INDIR/$f
done;
