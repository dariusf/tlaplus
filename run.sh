#!/usr/bin/env bash

tla2tools=tlatools/org.lamport.tlatools/dist/tla2tools.jar

compile() {
  ant -f tlatools/org.lamport.tlatools/customBuild.xml -Dtest.skip=true compile dist
}

pluscal() {
  java -cp "$tla2tools" pcal.trans "$@"
}

tlc() {
  java -cp "$tla2tools" tlc2.TLC "$@"
}

sany() {
  java -cp "$tla2tools" tla2sany.SANY "$@"
}

if [ ! -z ${COMPILE+x} ]; then
  compile
fi

# pluscal -label ~/refinement-mappings/PlusCal-Examples/TwoPhaseCommit/Chor.tla

pluscal -label ~/refinement-mappings/PlusCal-Examples/TwoPhaseCommit/Par.tla

# tlc -monitor ~/tla/Counter.tla

# tlc -monitor ~/refinement-mappings/trace-specs/2pc/TwoPhaseCommitFull.tla

# sany -d ~/tla/Counter.tla
