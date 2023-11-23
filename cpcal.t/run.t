
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

  $ cpluscal -nocfg Par.tla
  ++ cpluscal -nocfg Par.tla
  ++ pluscal -label -nocfg Par.tla
  ++ tlatools pcal.trans -label -nocfg Par.tla
  ++ name=pcal.trans
  ++ shift
  ++ set -x
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg Par.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coord:
  
  process (C = coord)
    variables
      x = 1;
  {
    par {
      x := x + 1;
    } and {
      x := x + 2;
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
  {
    par {
      skip;
    } and {
      skip;
    }
  }
  
  Final processes:
  
  process (proc_2 \in ( coord \X { "C_par_1" } ))
  {
    await pc [ Head ( self ) ] = "par_0";;
    x := x + 1;
  }
  process (proc_4 \in ( coord \X { "C_par_3" } ))
  {
    await pc [ Head ( self ) ] = "par_0";;
    x := x + 2;
  }
  process (C = coord)
    variables
      x = 1;
  {
    par_0:
    await \A v_5 \in ( coord \X { "C_par_1" , "C_par_3" } ) : pc [ v_5 ] = "Done";
  }
  process (proc_8 \in ( participants \X { "P_par_7" } ))
  {
    await pc [ Head ( self ) ] = "par_6";;
    skip;
  }
  process (proc_10 \in ( participants \X { "P_par_9" } ))
  {
    await pc [ Head ( self ) ] = "par_6";;
    skip;
  }
  process (P \in participants)
  {
    par_6:
    await \A v_11 \in ( participants \X { "P_par_7" , "P_par_9" } ) : pc [ v_11 ] = "Done";
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Par.tla written.
