
  $ tlaroot=.. source ../build.sh
  tla2tools at ../tlatools/org.lamport.tlatools/dist/tla2tools.jar

  $ cpluscal -nocfg Chor.tla
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg Chor.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of participants:
  
  process (P \in participants)
    variables
      committed = { };
  {
    Receive(coord, self, "prepare");
    committed := committed \union { << p , coord >> };
  }
  
  Projection of coord:
  
  process (C = coord)
  {
    all (p \in participants) {
      Send(p, self, "prepare")
      skip;
    }
  }
  
  Final processes:
  
  process (P \in participants)
    variables
      committed = { };
  {
    Receive(coord, self, "prepare");
    committed := committed \union { << p , coord >> };
  }
  process (proc_1 \in ( coord \X participants ))
  {
    await pc [ Head ( self ) ] = "fork_0";;
    Send(p, self, "prepare");
    skip;
  }
  process (C = coord)
  {
    fork_0:
    await \A p \in ( coord \X participants ) : pc [ p ] = "Done";
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Chor.tla written.

$ cpluscal -nocfg Par.tla | make_det
++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label Par.tla
pcal.trans Version 1.11 of 31 December 2020
Labels added.
Parsing completed.
Translation completed.
New file Par.tla written.
New file Par.cfg written.
