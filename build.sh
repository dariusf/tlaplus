#!/usr/bin/env bash

tlaroot=${tlaroot-.}
tla2tools=${tla2tools-tlatools/org.lamport.tlatools/dist/tla2tools.jar}

compile() {
  ant -f $tlaroot/tlatools/org.lamport.tlatools/customBuild.xml -Dtest.skip=true compile dist
}

test () {
  set -x
  rm benchmarks.t/*.go
  dune test
}

alias c=compile
alias t=test
alias d='dune promote'

tlatools() {
  name=$1
  shift
  java -XX:+UseParallelGC -cp "$tla2tools" "$name" "$@" 2>&1
}

pluscal() {
  tlatools pcal.trans "$@"
}

tlc() {
  tlatools tlc2.TLC "$@"
}

sany() {
  tlatools tla2sany.SANY "$@"
}

make_det() {
  # remove lines with timestamps and temp file names
  grep -v '^Starting...' | \
  grep -v '^Parsing file' | \
  grep -v '^Finished in'
}

# pluscal -label File.tla
# tlc -monitor File.tla
# sany -d File.tla
