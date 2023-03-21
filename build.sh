#!/usr/bin/env bash

# this file is meant to be sourced

tlaroot=${tlaroot-.}
tla2tools=${tla2tools-$tlaroot/tlatools/org.lamport.tlatools/dist/tla2tools.jar}

startup() {
  ls $tla2tools > /dev/null 2>&1 || { echo 'tla2tools not found. please set tlaroot'; unset tlaroot; unset tla2tools; return 1; }
  echo tla2tools at $tla2tools
}

startup

compile() {
  ant -f $tlaroot/tlatools/org.lamport.tlatools/customBuild.xml -Dtest.skip=true compile dist
}

test1() {
  set -x
  rm benchmarks.t/*.go
  dune test
}

alias c=compile
alias t=test1
alias d='dune promote'

tlatools() {
  name=$1
  shift
  set -x
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
