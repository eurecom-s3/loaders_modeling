#!/bin/bash

GHIDRAPATH=${1:-/home/dario/tools/ghidra/build/dist/ghidra_9.2_DEV/support/analyzeHeadless}
GHIDRAPROJ=${2:-/home/dario/phd/loaders_modeling/ghidraproj}
INDIR=${3:-/home/dario/phd/loaders_modeling/lang_parser/allcombo}
OUTDIR=${4:-/tmp/ghidraalldumps}

mkdir -p $OUTDIR

rm -r $GHIDRAPROJ
mkdir $GHIDRAPROJ

TESTCASES=$(ls $INDIR)
for f in $TESTCASES
do
    if [[ $f == *"cond"* ]]; then
	continue
    fi;
    $GHIDRAPATH $GHIDRAPROJ ghidratest -loader PeLoader -postscript ghidradumpmem.py -import $INDIR/$f
done;
