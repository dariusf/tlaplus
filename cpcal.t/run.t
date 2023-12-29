
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
  Projection of coordinators:
  
  process (C \in coordinators)
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
  
  process (C \in coordinators)
    variables
      x = 1;
  {
    par_0:
    await \A v_5 \in ( { "C_par_1" , "C_par_3" } \X { coordinators } ) : pc [ v_5 ] = "Done";
  }
  process (P \in participants)
  {
    skip;
  }
  process (proc_2 \in ( "C_par_1" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    x := x + 1;
  }
  process (proc_4 \in ( "C_par_3" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    x := x + 2;
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Par.tla written.

  $ cpluscal -nocfg ParNested.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coordinators:
  
  process (C \in coordinators)
    variables
      x = 1;
  {
    all (p \in participants) {
      par {
        par {
          x := x + 1;
        } and {
          x := x + 3;
        }
      } and {
        x := x + 2;
      }
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
  {
    skip;
  }
  
  Final processes:
  
  process (C \in coordinators)
    variables
      x = 1;
  {
    fork_12:
    await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
  }
  process (P \in participants)
  {
    skip;
  }
  process (proc_10 \in ( "C_par_9" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    x := x + 2;
  }
  process (proc_13 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_12";
    par_0:
    await \A v_11 \in ( { "C_par_1" , "C_par_9" } \X { coordinators } ) : pc [ v_11 ] = "Done";
  }
  process (proc_4 \in ( "C_par_3" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_2";
    x := x + 1;
  }
  process (proc_6 \in ( "C_par_5" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_2";
    x := x + 3;
  }
  process (proc_8 \in ( "C_par_1" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    par_2:
    await \A v_7 \in ( { "C_par_3" , "C_par_5" } \X { coordinators } ) : pc [ v_7 ] = "Done";
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file ParNested.tla written.

  $ cpluscal -nocfg Cancel.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of coordinators:
  
  process (C \in coordinators)
  {
    skip;
  }
  
  Projection of participants:
  
  process (P \in participants)
    variables
      x = 0;
  {
    all (c \in coordinators) {
      task P, "a" {
        x := x + 2;
      }
    }
  }
  
  Final processes:
  
  process (C \in coordinators)
  {
    skip;
  }
  process (P \in participants)
    variables
      x = 0;
  {
    fork_0:
    await \A c \in ( coordinators \X participants ) : pc [ c ] = "Done";
  }
  process (proc_1 \in ( coordinators \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_0";
    if (~ cancelled_a) {
      x := x + 2;
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
  Projection of coordinators:
  
  process (C = coordinators)
    variables
      y = 3;
  {
    par {
      all (p \in participants) {
        while (y [ self ] > 1) {
          Send(self, p, 5);
          y := y - 1;
          skip;
        }
      }
    } and {
      all (c \in coordinators \ { self }) {
        all (p \in participants) {
          while (y [ c ] > 1) {
            skip;
            skip;
            skip;
          }
        }
      }
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
    variables
      x = 1;
  {
    all (c \in coordinators) {
      par {
        while (x [ self ] < 3) {
          Receive(c, self, 5);
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
  }
  
  Final processes:
  
  process (C = coordinators)
    variables
      y = 3;
  {
    par_11:
    await \A v_16 \in ( { "C_par_12" , "C_par_14" } \X { coordinators } ) : pc [ v_16 ] = "Done";
  }
  process (P \in participants)
    variables
      x = 1;
  {
    fork_9:
    await \A c \in ( coordinators \X participants ) : pc [ c ] = "Done";
  }
  process (proc_10 \in ( coordinators \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_9";
    par_0:
    await \A v_5 \in ( { "P_par_1" , "P_par_3" } \X { participants } ) : pc [ v_5 ] = "Done";
  }
  process (proc_13 \in ( "C_par_12" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_11";
    fork_17:
    await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
  }
  process (proc_15 \in ( "C_par_14" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_11";
    fork_20:
    await \A c \in ( coordinators \ { Head ( Tail ( self ) ) } \X coordinators ) : pc [ c ] = "Done";
  }
  process (proc_18 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_17";
    while (y [ Head ( Tail ( self ) ) ] > 1) {
      comm_19:
      Send(Head ( Tail ( self ) ), Head(self), 5);
      y := y - 1;
      skip;
    }
  }
  process (proc_2 \in ( "P_par_1" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    while (x [ Head(Tail(self)) ] < 3) {
      comm_6:
      Receive(c, Head(Tail(self)), 5);
      skip;
      x := x + 1;
    }
  }
  process (proc_22 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_21";
    while (y [ c ] > 1) {
      skip;
      skip;
      skip;
    }
  }
  process (proc_23 \in ( coordinators \ { Head ( Tail ( self ) ) } \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_20";
    fork_21:
    await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
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
  Projection of coordinators:
  
  process (C \in coordinators)
  {
    par {
      task C, "phase1" {
        all (p \in participants) {
          Send(self, p, "prepare");
          either {
            Receive(p, self, "prepared");
          } or {
            Receive(p, self, "aborted");
          }
        }
      }
      if (aborted) {
        all (p \in participants) {
          Send(self, p, "abort");
          Receive(p, self, "aborted");
        }
      } else {
        all (p \in participants) {
          Send(self, p, "commit");
          Receive(p, self, "committed");
        }
      }
    } and {
      all (c \in coordinators \ { self }) {
        if (aborted) {
          skip;
        } else {
          skip;
        }
      }
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
  {
    all (c \in coordinators) {
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
  }
  
  Final processes:
  
  process (C \in coordinators)
  {
    par_0:
    await \A v_5 \in ( { "C_par_1" , "C_par_3" } \X { coordinators } ) : pc [ v_5 ] = "Done";
  }
  process (P \in participants)
  {
    fork_21:
    await \A c \in ( coordinators \X participants ) : pc [ c ] = "Done";
  }
  process (proc_11 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_10";
    comm_17:
    Send(Head ( Tail ( self ) ), Head(self), "commit");
    comm_18:
    Receive(Head(self), Head ( Tail ( self ) ), "committed");
  }
  process (proc_2 \in ( "C_par_1" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    if (~ cancelled_phase1) {
      fork_6:
      await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
    } else {
      skip;
    }
    if (aborted) {
      fork_8:
      await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
    } else {
      fork_10:
      await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
    }
  }
  process (proc_20 \in ( coordinators \ { Head ( Tail ( self ) ) } \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_19";
    if (aborted) {
      skip;
    } else {
      skip;
    }
  }
  process (proc_22 \in ( coordinators \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_21";
    comm_23:
    Receive(Head(self), Head ( Tail ( self ) ), "prepare");
    either {
      comm_24:
      Send(Head ( Tail ( self ) ), Head(self), "prepared");
    } or {
      comm_25:
      Send(Head ( Tail ( self ) ), Head(self), "aborted");
    }
    if (aborted) {
      comm_26:
      Receive(Head(self), Head ( Tail ( self ) ), "abort");
      comm_27:
      Send(Head ( Tail ( self ) ), Head(self), "aborted");
    } else {
      comm_28:
      Receive(Head(self), Head ( Tail ( self ) ), "commit");
      comm_29:
      Send(Head ( Tail ( self ) ), Head(self), "committed");
    }
  }
  process (proc_4 \in ( "C_par_3" \X { coordinators } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    fork_19:
    await \A c \in ( coordinators \ { Head ( Tail ( self ) ) } \X coordinators ) : pc [ c ] = "Done";
  }
  process (proc_7 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_6";
    comm_12:
    Send(Head ( Tail ( self ) ), Head(self), "prepare");
    either {
      comm_13:
      Receive(Head(self), Head ( Tail ( self ) ), "prepared");
    } or {
      comm_14:
      Receive(Head(self), Head ( Tail ( self ) ), "aborted");
    }
  }
  process (proc_9 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_8";
    comm_15:
    Send(Head ( Tail ( self ) ), Head(self), "abort");
    comm_16:
    Receive(Head(self), Head ( Tail ( self ) ), "aborted");
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
