
  $ tlaroot=.. source ../build.sh
  tla2tools at ../tlatools/org.lamport.tlatools/dist/tla2tools.jar

  $ function assert_termination() { grep 'Stuttering\|The depth of'; }

  $ cpluscal -nocfg Hello.tla 2> /dev/null
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coordinators:
  
  process (C \in coordinators)
  {
    all (p \in participants) {
      Send(self, p, "a");
      Receive(p, self, "b");
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
  {
    all (c \in coordinators) {
      Receive(c, self, "a");
      Send(self, c, "b");
    }
  }
  
  Final processes:
  
  process (C \in coordinators)
  {
    fork_4:
    await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
  }
  process (P \in participants)
  {
    fork_0:
    await \A c \in ( coordinators \X participants ) : pc [ c ] = "Done";
  }
  process (proc_1 \in ( coordinators \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_0";
    comm_2:
    Receive(Head(self), Head ( Tail ( self ) ), "a");
    comm_3:
    Send(Head ( Tail ( self ) ), Head(self), "b");
  }
  process (proc_5 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_4";
    comm_6:
    Send(Head ( Tail ( self ) ), Head(self), "a");
    comm_7:
    Receive(Head(self), Head ( Tail ( self ) ), "b");
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Hello.tla written.

  $ tlc Hello.tla 2> /dev/null | assert_termination
  State 29: Stuttering
  The depth of the complete state graph search is 29.

  $ cpluscal -nocfg Assign.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coordinators:
  
  process (C \in coordinators)
  {
    skip;
  }
  
  Projection of participants:
  
  process (P \in participants)
    variables
      committed = { };
  {
    all (c \in coordinators) {
      committed := committed \union { << self , c >> };
    }
  }
  
  Final processes:
  
  process (C \in coordinators)
  {
    skip;
  }
  process (P \in participants)
    variables
      committed = { };
  {
    fork_0:
    await \A c \in ( coordinators \X participants ) : pc [ c ] = "Done";
  }
  process (proc_1 \in ( coordinators \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_0";
    committed := committed \union { << Head ( Tail ( self ) ) , Head(self) >> };
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Assign.tla written.

  $ tlc Assign.tla 2> /dev/null | assert_termination
  State 9: Stuttering
  The depth of the complete state graph search is 9.

  $ cpluscal -nocfg Par.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coord:
  
  process (C = coord)
    variables
      x = 1;
  {
    skip;
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
    skip;
  }
  process (P \in participants)
  {
    skip;
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Par.tla written.

  $ cpluscal -nocfg Cancel.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of participants:
  
  process (P \in participants)
    variables
      x = 0;
  {
    task P, "a" {
      cancel a;
    }
  }
  
  Final processes:
  
  process (P \in participants)
    variables
      x = 0;
  {
    if (~ cancelled_a) {
      cancelled_a := TRUE;
    } else {
      skip;
    }
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Cancel.tla written.

  $ cpluscal -nocfg While.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coord:
  
  process (C = coord)
    variables
      y = 3;
  {
    all (p \in participants) {
      while (y > 1) {
        skip;
        skip;
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
        x := x + 1;
      }
    } and {
      all (p \in participants \ { self }) {
        while (x [ p ] < 3) {
          skip;
          skip;
          skip;
        }
      }
    }
  }
  
  Final processes:
  
  process (C = coord)
    variables
      y = 3;
  {
    fork_9:
    await \A p \in ( participants \X coord ) : pc [ p ] = "Done";
  }
  process (P \in participants)
    variables
      x = 1;
  {
    par_0:
    await \A v_5 \in ( { "P_par_1" , "P_par_3" } \X { participants } ) : pc [ v_5 ] = "Done";
  }
  process (proc_10 \in ( participants \X coord ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_9";
    while (y > 1) {
      skip;
      skip;
      skip;
    }
  }
  process (proc_2 \in ( "P_par_1" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    while (x [ Head(Tail(self)) ] < 3) {
      comm_6:
      Receive(coord, Head(Tail(self)), 5);
      skip;
      x := x + 1;
    }
  }
  process (proc_4 \in ( "P_par_3" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    fork_7:
    await \A p \in ( participants \ { Head ( Tail ( self ) ) } \X participants ) : pc [ p ] = "Done";
  }
  process (proc_8 \in ( participants \ { Head ( Tail ( self ) ) } \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_7";
    while (x [ Head(self) ] < 3) {
      skip;
      skip;
      skip;
    }
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file While.tla written.

  $ cpluscal -nocfg TwoPhaseCommit.tla
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
    Receive(c, self, "prepare");
    either {
      Send(self, c, "prepared");
    } or {
      Send(self, c, "aborted");
    }
    if (aborted) {
      Receive(c, self, "abort");
      Send(self, c, "aborted");
    } else {
      Receive(c, self, "commit");
      Send(self, c, "committed");
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
    comm_2:
    Receive(c, Head(Tail(self)), "prepare");
    either {
      comm_3:
      Send(Head(Tail(self)), c, "prepared");
    } or {
      comm_4:
      Send(Head(Tail(self)), c, "aborted");
    }
    if (aborted) {
      comm_5:
      Receive(c, Head(Tail(self)), "abort");
      comm_6:
      Send(Head(Tail(self)), c, "aborted");
    } else {
      comm_7:
      Receive(c, Head(Tail(self)), "commit");
      comm_8:
      Send(Head(Tail(self)), c, "committed");
    }
  }
  process (proc_1 \in ( participants \X c ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_0";
    cancelled_phase1 := TRUE;
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file TwoPhaseCommit.tla written.

  $ cpluscal -nocfg SelfSend.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of participants:
  
  process (P \in participants)
  {
    all (q \in participants \ { self }) {
      Send(self, q, "prepare");
    }
  }
  
  Final processes:
  
  process (P \in participants)
  {
    fork_0:
    await \A q \in ( participants \ { Head ( Tail ( self ) ) } \X participants ) : pc [ q ] = "Done";
  }
  process (proc_1 \in ( participants \ { Head ( Tail ( self ) ) } \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_0";
    comm_2:
    Send(Head ( Tail ( self ) ), Head(self), "prepare");
  }
  Projection of ps:
  
  process (P1 \in ps)
  {
    all (q \in qs) {
      Send(self, q, "prepare");
    }
  }
  
  Projection of qs:
  
  process (Q \in qs)
  {
    all (p \in ps) {
      Receive(p, self, "prepare");
    }
  }
  
  Final processes:
  
  process (P1 \in ps)
  {
    fork_6:
    await \A q \in ( qs \X ps ) : pc [ q ] = "Done";
  }
  process (Q \in qs)
  {
    fork_3:
    await \A p \in ( ps \X qs ) : pc [ p ] = "Done";
  }
  process (proc_4 \in ( ps \X qs ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_3";
    comm_5:
    Receive(Head(self), Head ( Tail ( self ) ), "prepare");
  }
  process (proc_7 \in ( qs \X ps ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_6";
    comm_8:
    Send(Head ( Tail ( self ) ), Head(self), "prepare");
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file SelfSend.tla written.

$ cpluscal -nocfg NBAC.tla
$ cpluscal -nocfg Raft.tla
