
  $ tlaroot=.. source ../build.sh
  tla2tools at ../tlatools/org.lamport.tlatools/dist/tla2tools.jar

  $ cpluscal -nocfg Hello.tla
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg Hello.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coordinators:
  
  process (C \in coordinators)
  {
    all (p \in participants) {
      Send(self, p, a);
      Receive(p, self, b);
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
  {
    all (c \in coordinators) {
      Receive(c, self, a);
      Send(self, c, b);
    }
  }
  
  Final processes:
  
  process (C \in coordinators)
  {
    fork_2:
    await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
  }
  process (P \in participants)
  {
    fork_0:
    await \A c \in ( coordinators \X participants ) : pc [ c ] = "Done";
  }
  process (proc_1 \in ( coordinators \X participants ))
  {
    await pc [ Tail ( self ) ] = "fork_0";
    Receive(Head(self), Tail ( self ), a);
    Send(Tail ( self ), Head(self), b);
  }
  process (proc_3 \in ( participants \X coordinators ))
  {
    await pc [ Tail ( self ) ] = "fork_2";
    Send(Tail ( self ), Head(self), a);
    Receive(Head(self), Tail ( self ), b);
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Hello.tla written.

  $ cpluscal -nocfg Chor.tla
  ++ cpluscal -nocfg Chor.tla
  ++ pluscal -label -nocfg Chor.tla
  ++ tlatools pcal.trans -label -nocfg Chor.tla
  ++ name=pcal.trans
  ++ shift
  ++ set -x
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg Chor.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of participants:
  
  process (P \in participants)
    variables
      committed = { };
  {
    par {
      committed[ self ] := committed [ self ] \union { << self , coord >> };
    } and {
      all (p \in participants \ { self }) {
        committed[ p ] := committed [ p ] \union { << p , coord >> };
      }
    }
  }
  
  Final processes:
  
  process (P \in participants)
    variables
      committed = { };
  {
    par_0:
    await \A v_5 \in ( { "P_par_1" , "P_par_3" } \X { participants } ) : pc [ v_5 ] = "Done";
  }
  process (proc_2 \in ( "P_par_1" \X { participants } ))
  {
    await pc [ Tail ( self ) ] = "par_0";
    committed[ Tail(self) ] := committed [ Tail(self) ] \union { << Tail(self) , coord >> };
  }
  process (proc_4 \in ( "P_par_3" \X { participants } ))
  {
    await pc [ Tail ( self ) ] = "par_0";
    fork_6:
    await \A p \in ( participants \ { Tail ( self ) } \X participants ) : pc [ p ] = "Done";
  }
  process (proc_7 \in ( participants \ { Tail ( self ) } \X participants ))
  {
    await pc [ Tail ( self ) ] = "fork_6";
    committed[ Head(self) ] := committed [ Head(self) ] \union { << Head(self) , coord >> };
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
    skip;
  }
  
  Final processes:
  
  process (C = coord)
    variables
      x = 1;
  {
    par_0:
    await \A v_5 \in ( { "C_par_1" , "C_par_3" } \X { coord } ) : pc [ v_5 ] = "Done";
  }
  process (P \in participants)
  {
    skip;
  }
  process (proc_2 \in ( "C_par_1" \X { coord } ))
  {
    await pc [ Tail ( self ) ] = "par_0";
    x := x + 1;
  }
  process (proc_4 \in ( "C_par_3" \X { coord } ))
  {
    await pc [ Tail ( self ) ] = "par_0";
    x := x + 2;
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
    task P, "a" {
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
      await \A v_5 \in ( { "P_par_1" , "P_par_3" } \X { participants } ) : pc [ v_5 ] = "Done";
    } else {
      skip;
    }
  }
  process (proc_2 \in ( "P_par_1" \X { participants } ))
  {
    await pc [ Tail ( self ) ] = "par_0";
    cancelled_a := TRUE;
  }
  process (proc_4 \in ( "P_par_3" \X { participants } ))
  {
    await pc [ Tail ( self ) ] = "par_0";
    x := x + 2;
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Cancel.tla written.

  $ cpluscal -nocfg While.tla
  ++ cpluscal -nocfg While.tla
  ++ pluscal -label -nocfg While.tla
  ++ tlatools pcal.trans -label -nocfg While.tla
  ++ name=pcal.trans
  ++ shift
  ++ set -x
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg While.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coord:
  
  process (C = coord)
    variables
      y = 3;
  {
    all (p \in participants) {
      while (y > 1) {
        skip;
        y := y - 1;
        skip;
      }
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
    variables
      x = 1;
  {
    par {
      while (x [ self ] < 3) {
        Receive(coord, self, 5);
        skip;
        x[ self ] := x [ self ] + 1;
      }
    } and {
      all (p \in participants \ { self }) {
        while (x [ p ] < 3) {
          skip;
          skip;
          x[ p ] := x [ p ] + 1;
        }
      }
    }
  }
  
  Final processes:
  
  process (C = coord)
    variables
      y = 3;
  {
    fork_8:
    await \A p \in ( participants \X coord ) : pc [ p ] = "Done";
  }
  process (P \in participants)
    variables
      x = 1;
  {
    par_0:
    await \A v_5 \in ( { "P_par_1" , "P_par_3" } \X { participants } ) : pc [ v_5 ] = "Done";
  }
  process (proc_2 \in ( "P_par_1" \X { participants } ))
  {
    await pc [ Tail ( self ) ] = "par_0";
    while (x [ Tail(self) ] < 3) {
      Receive(coord, Tail(self), 5);
      skip;
      x[ Tail(self) ] := x [ Tail(self) ] + 1;
    }
  }
  process (proc_4 \in ( "P_par_3" \X { participants } ))
  {
    await pc [ Tail ( self ) ] = "par_0";
    fork_6:
    await \A p \in ( participants \ { Tail ( self ) } \X participants ) : pc [ p ] = "Done";
  }
  process (proc_7 \in ( participants \ { Tail ( self ) } \X participants ))
  {
    await pc [ Tail ( self ) ] = "fork_6";
    while (x [ Head(self) ] < 3) {
      skip;
      skip;
      x[ Head(self) ] := x [ Head(self) ] + 1;
    }
  }
  process (proc_9 \in ( participants \X coord ))
  {
    await pc [ Tail ( self ) ] = "fork_8";
    while (y > 1) {
      skip;
      y := y - 1;
      skip;
    }
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file While.tla written.

  $ cpluscal -nocfg TwoPhaseCommit.tla
  ++ cpluscal -nocfg TwoPhaseCommit.tla
  ++ pluscal -label -nocfg TwoPhaseCommit.tla
  ++ tlatools pcal.trans -label -nocfg TwoPhaseCommit.tla
  ++ name=pcal.trans
  ++ shift
  ++ set -x
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg TwoPhaseCommit.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of c:
  
  process (C = c)
  {
    task C, "phase1" {
      all (p \in participants) {
        cancel phase1;
      }
    }
    if (aborted) {
      skip;
    } else {
      skip;
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
  {
    Receive(c, self, prepare);
    either {
      Send(self, c, prepared);
    } or {
      Send(self, c, aborted);
    }
    if (aborted) {
      Receive(c, self, abort);
      Send(self, c, aborted);
    } else {
      Receive(c, self, commit);
      Send(self, c, committed);
    }
  }
  
  Final processes:
  
  process (C = c)
  {
    if (~ cancelled_phase1) {
      fork_0:
      await \A p \in ( participants \X c ) : pc [ p ] = "Done";
    } else {
      skip;
    }
    if (aborted) {
      skip;
    } else {
      skip;
    }
  }
  process (P \in participants)
  {
    Receive(c, Tail(self), prepare);
    either {
      Send(Tail(self), c, prepared);
    } or {
      Send(Tail(self), c, aborted);
    }
    if (aborted) {
      Receive(c, Tail(self), abort);
      Send(Tail(self), c, aborted);
    } else {
      Receive(c, Tail(self), commit);
      Send(Tail(self), c, committed);
    }
  }
  process (proc_1 \in ( participants \X c ))
  {
    await pc [ Tail ( self ) ] = "fork_0";
    cancelled_phase1 := TRUE;
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file TwoPhaseCommit.tla written.

  $ cpluscal -nocfg SelfSend.tla
  ++ cpluscal -nocfg SelfSend.tla
  ++ pluscal -label -nocfg SelfSend.tla
  ++ tlatools pcal.trans -label -nocfg SelfSend.tla
  ++ name=pcal.trans
  ++ shift
  ++ set -x
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label -nocfg SelfSend.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of participants:
  
  process (P \in participants)
  {
    all (q \in participants \ { self }) {
      Send(self, q, prepare);
    }
  }
  
  Final processes:
  
  process (P \in participants)
  {
    fork_0:
    await \A q \in ( participants \ { Tail ( self ) } \X participants ) : pc [ q ] = "Done";
  }
  process (proc_1 \in ( participants \ { Tail ( self ) } \X participants ))
  {
    await pc [ Tail ( self ) ] = "fork_0";
    Send(Tail ( self ), Head(self), prepare);
  }
  Projection of ps:
  
  process (P1 \in ps)
  {
    all (q \in qs) {
      Send(self, q, prepare);
    }
  }
  
  Projection of qs:
  
  process (Q \in qs)
  {
    all (p \in ps) {
      Receive(p, self, prepare);
    }
  }
  
  Final processes:
  
  process (P1 \in ps)
  {
    fork_4:
    await \A q \in ( qs \X ps ) : pc [ q ] = "Done";
  }
  process (Q \in qs)
  {
    fork_2:
    await \A p \in ( ps \X qs ) : pc [ p ] = "Done";
  }
  process (proc_3 \in ( ps \X qs ))
  {
    await pc [ Tail ( self ) ] = "fork_2";
    Receive(Head(self), Tail ( self ), prepare);
  }
  process (proc_5 \in ( qs \X ps ))
  {
    await pc [ Tail ( self ) ] = "fork_4";
    Send(Tail ( self ), Head(self), prepare);
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file SelfSend.tla written.

$ cpluscal -nocfg NBAC.tla
$ cpluscal -nocfg Raft.tla
