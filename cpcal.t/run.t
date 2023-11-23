
  $ tlaroot=.. source ../build.sh
  tla2tools at ../tlatools/org.lamport.tlatools/dist/tla2tools.jar

  $ cpluscal -nocfg Chor.tla
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg Chor.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coord:
  
  process (C = coord)
  {
    all (p \in participants) {
      Send(p, self, "prepare");
      skip;
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
    variables
      committed = { };
  {
    Receive(coord, self, "prepare");
    committed := committed \union { << p , coord >> };
  }
  
  Final processes:
  
  process (C = coord)
  {
    fork_0:
    await \A p \in ( coord \X participants ) : pc [ p ] = "Done";
  }
  process (P \in participants)
    variables
      committed = { };
  {
    Receive(coord, self, "prepare");
    committed := committed \union { << p , coord >> };
  }
  process (proc_1 \in ( coord \X participants ))
  {
    await pc [ Head ( self ) ] = "fork_0";
    Send(p, self, "prepare");
    skip;
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
  
  process (C = coord)
    variables
      x = 1;
  {
    par_6:
    await \A v_11 \in ( coord \X { "C_par_7" , "C_par_9" } ) : pc [ v_11 ] = "Done";
  }
  process (P \in participants)
  {
    par_0:
    await \A v_5 \in ( participants \X { "P_par_1" , "P_par_3" } ) : pc [ v_5 ] = "Done";
  }
  process (proc_10 \in ( coord \X { "C_par_9" } ))
  {
    await pc [ Head ( self ) ] = "par_6";
    x := x + 2;
  }
  process (proc_2 \in ( participants \X { "P_par_1" } ))
  {
    await pc [ Head ( self ) ] = "par_0";
    skip;
  }
  process (proc_4 \in ( participants \X { "P_par_3" } ))
  {
    await pc [ Head ( self ) ] = "par_0";
    skip;
  }
  process (proc_8 \in ( coord \X { "C_par_7" } ))
  {
    await pc [ Head ( self ) ] = "par_6";
    x := x + 1;
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Par.tla written.

  $ cpluscal -nocfg Cancel.tla
  ++ cpluscal -nocfg Cancel.tla
  ++ pluscal -label -nocfg Cancel.tla
  ++ tlatools pcal.trans -label -nocfg Cancel.tla
  ++ name=pcal.trans
  ++ shift
  ++ set -x
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg Cancel.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of participants:
  
  process (P \in participants)
    variables
      x = 0;
  {
    task P, a {
      par {
        cancel a;
      } and {
        x := x + 2;
      }
    }
  }
  
  Final processes:
  
  process (P \in participants)
    variables
      x = 0;
  {
    if (~ cancelled_a) {
      par_0:
      await \A v_5 \in ( participants \X { "P_par_1" , "P_par_3" } ) : pc [ v_5 ] = "Done";
    } else {
      skip;
    }
  }
  process (proc_2 \in ( participants \X { "P_par_1" } ))
  {
    await pc [ Head ( self ) ] = "par_0";
    cancelled_a := TRUE;
  }
  process (proc_4 \in ( participants \X { "P_par_3" } ))
  {
    await pc [ Head ( self ) ] = "par_0";
    x := x + 2;
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Cancel.tla written.
