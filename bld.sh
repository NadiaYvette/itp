#!/bin/sh
GHC=ghc-9.12.1
CABAL=cabal-3.14.1.1
CABAL_OPTS="--keep-going --jobs=256 --with-compiler=${GHC} --preference=newer"
SRC=./src/Numeric/ITP.lhs
LTX=./doc/ITP.ltx

ckret ()
{
	if [ $1 -ne 0 ]
	then
		exit $1
	fi
	return 0
}

export TEXINPUTS="$(pwd)/doc:"
export BIBINPUTS="$(pwd)/bib:"
$CABAL $CABAL_OPTS build itp
ckret $?
lhs2TeX $SRC -o $LTX
ckret $?
for n in 1 2 3
do
	pdflatex -output-directory ./doc/ $LTX \
	&& (cd doc; bibtex ITP) \
	&& pdflatex -output-directory ./doc/ $LTX
	ckret $?
done
