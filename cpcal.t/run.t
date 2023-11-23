
  $ tlaroot=.. source ../build.sh
  tla2tools at ../tlatools/org.lamport.tlatools/dist/tla2tools.jar

  $ pluscal -label Chor.tla

$ pluscal -label Par.tla | make_det
++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label Par.tla
pcal.trans Version 1.11 of 31 December 2020
Labels added.
Parsing completed.
Translation completed.
New file Par.tla written.
New file Par.cfg written.
