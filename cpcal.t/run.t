
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
    if (~ cancelled_phase1) {
      fork_0:
      await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
    } else {
      skip;
    }
    if (aborted) {
      fork_2:
      await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
    } else {
      fork_4:
      await \A p \in ( participants \X coordinators ) : pc [ p ] = "Done";
    }
  }
  process (P \in participants)
  {
    fork_13:
    await \A c \in ( coordinators \X participants ) : pc [ c ] = "Done";
  }
  process (proc_1 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_0";
    comm_6:
    Send(Head ( Tail ( self ) ), Head(self), "prepare");
    either {
      comm_7:
      Receive(Head(self), Head ( Tail ( self ) ), "prepared");
    } or {
      comm_8:
      Receive(Head(self), Head ( Tail ( self ) ), "aborted");
    }
  }
  process (proc_14 \in ( coordinators \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_13";
    comm_15:
    Receive(Head(self), Head ( Tail ( self ) ), "prepare");
    either {
      comm_16:
      Send(Head ( Tail ( self ) ), Head(self), "prepared");
    } or {
      comm_17:
      Send(Head ( Tail ( self ) ), Head(self), "aborted");
    }
    if (aborted) {
      comm_18:
      Receive(Head(self), Head ( Tail ( self ) ), "abort");
      comm_19:
      Send(Head ( Tail ( self ) ), Head(self), "aborted");
    } else {
      comm_20:
      Receive(Head(self), Head ( Tail ( self ) ), "commit");
      comm_21:
      Send(Head ( Tail ( self ) ), Head(self), "committed");
    }
  }
  process (proc_3 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_2";
    comm_9:
    Send(Head ( Tail ( self ) ), Head(self), "abort");
    comm_10:
    Receive(Head(self), Head ( Tail ( self ) ), "aborted");
  }
  process (proc_5 \in ( participants \X coordinators ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_4";
    comm_11:
    Send(Head ( Tail ( self ) ), Head(self), "commit");
    comm_12:
    Receive(Head(self), Head ( Tail ( self ) ), "committed");
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

  $ cpluscal -nocfg Paxos.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of acceptors:
  
  process (A \in acceptors)
    variables
      highest_proposal = << 0 , 0 >>;
      accepted_proposal = << 0 , 0 >>;
      accepted_value = 0;
  {
    all (p \in proposers) {
      par {
        Receive(p, self, << "prepare" , << p , proposal >> >>);
        if (n > highest_proposal) {
          highest_proposal := n;
          Send(self, p, << "promise" , [ cp |-> accepted_proposal , cv |-> accepted_value ] >>);
        } else {
        }
      } and {
        await Size ( promise_responses ) > majority;
      }
    }
  }
  
  Projection of learners:
  
  process (L \in learners)
  {
    all (p \in proposers) {
      await Size ( promise_responses ) > majority;
      all (a1 \in promise_responses) {
        if (msg . pn = highest_proposal) {
          Receive(a1, self, "accept");
        } else {
        }
      }
    }
  }
  
  Projection of proposers:
  
  process (P \in proposers)
    variables
      proposal = 0;
      value = 1;
      cp = << 0 , 0 >>;
      majority = size ( acceptors ) / 2 + 1;
      promise_responses = { };
  {
    par {
      par {
        proposal := proposal + 1;
        all (a \in acceptors) {
          Send(self, a, << "prepare" , << self , proposal >> >>);
          if (n > highest_proposal) {
            Receive(a, self, << "promise" , [ cp |-> accepted_proposal , cv |-> accepted_value ] >>);
            promise_responses := promise_responses \union { a };
            if (resp . cp > << 0 , 0 >> /\ resp . cp > cp) {
              cp := resp . cp;
              value := resp . cv;
            } else {
            }
          } else {
          }
        }
      } and {
        await Size ( promise_responses ) > majority;
        all (a1 \in promise_responses) {
          Send(self, a1, << "propose" , [ pn |-> proposal , pv |-> value , a1 |-> a1 ] >>);
          if (msg . pn = highest_proposal) {
            Receive(a1, self, "accept");
          } else {
          }
        }
      }
    } and {
      all (p \in proposers \ { self }) {
        await Size ( promise_responses ) > majority;
      }
    }
  }
  
  Final processes:
  
  process (A \in acceptors)
    variables
      highest_proposal = << 0 , 0 >>;
      accepted_proposal = << 0 , 0 >>;
      accepted_value = 0;
  {
    fork_35:
    await \A p \in ( proposers \X acceptors ) : pc [ p ] = "Done";
  }
  process (L \in learners)
  {
    fork_22:
    await \A p \in ( proposers \X learners ) : pc [ p ] = "Done";
  }
  process (P \in proposers)
    variables
      proposal = 0;
      value = 1;
      cp = << 0 , 0 >>;
      majority = size ( acceptors ) / 2 + 1;
      promise_responses = { };
  {
    par_0:
    await \A v_11 \in ( { "P_par_1" , "P_par_9" } \X { proposers } ) : pc [ v_11 ] = "Done";
  }
  process (proc_10 \in ( "P_par_9" \X { proposers } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    fork_20:
    await \A p \in ( proposers \ { Head ( Tail ( self ) ) } \X proposers ) : pc [ p ] = "Done";
  }
  process (proc_13 \in ( acceptors \X proposers ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_12";
    comm_14:
    Send(Head ( Tail ( self ) ), Head(self), << "prepare" , << Head ( Tail ( self ) ) , proposal >> >>);
    if (n > highest_proposal) {
      comm_15:
      Receive(Head(self), Head ( Tail ( self ) ), << "promise" , [ cp |-> accepted_proposal , cv |-> accepted_value ] >>);
      promise_responses := promise_responses \union { Head(self) };
      if (resp . cp > << 0 , 0 >> /\ resp . cp > cp) {
        cp := resp . cp;
        value := resp . cv;
      } else {
      }
    } else {
    }
  }
  process (proc_17 \in ( promise_responses \X proposers ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_16";
    comm_18:
    Send(Head ( Tail ( self ) ), Head(self), << "propose" , [ pn |-> proposal , pv |-> value , Head(self) |-> Head(self) ] >>);
    if (msg . pn = highest_proposal) {
      comm_19:
      Receive(Head(self), Head ( Tail ( self ) ), "accept");
    } else {
    }
  }
  process (proc_21 \in ( proposers \ { Head ( Tail ( self ) ) } \X proposers ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_20";
    await Size ( promise_responses ) > majority;
  }
  process (proc_24 \in ( promise_responses \X learners ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_23";
    if (msg . pn = highest_proposal) {
      comm_26:
      Receive(Head(self), Head ( Tail ( self ) ), "accept");
    } else {
    }
  }
  process (proc_25 \in ( proposers \X learners ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_22";
    await Size ( promise_responses ) > majority;
    fork_23:
    await \A a1 \in ( promise_responses \X learners ) : pc [ a1 ] = "Done";
  }
  process (proc_29 \in ( "A_par_28" \X { acceptors } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_27";
    comm_33:
    Receive(p, Head(Tail(self)), << "prepare" , << p , proposal >> >>);
    if (n > highest_proposal) {
      highest_proposal := n;
      comm_34:
      Send(Head(Tail(self)), p, << "promise" , [ cp |-> accepted_proposal , cv |-> accepted_value ] >>);
    } else {
    }
  }
  process (proc_31 \in ( "A_par_30" \X { acceptors } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_27";
    await Size ( promise_responses ) > majority;
  }
  process (proc_36 \in ( proposers \X acceptors ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_35";
    par_27:
    await \A v_32 \in ( { "A_par_28" , "A_par_30" } \X { acceptors } ) : pc [ v_32 ] = "Done";
  }
  process (proc_4 \in ( "P_par_3" \X { proposers } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_2";
    proposal := proposal + 1;
    fork_12:
    await \A a \in ( acceptors \X proposers ) : pc [ a ] = "Done";
  }
  process (proc_6 \in ( "P_par_5" \X { proposers } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_2";
    await Size ( promise_responses ) > majority;
    fork_16:
    await \A a1 \in ( promise_responses \X proposers ) : pc [ a1 ] = "Done";
  }
  process (proc_8 \in ( "P_par_1" \X { proposers } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    par_2:
    await \A v_7 \in ( { "P_par_3" , "P_par_5" } \X { proposers } ) : pc [ v_7 ] = "Done";
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file Paxos.tla written.

  $ cpluscal -nocfg NBAC.tla
  pcal.trans Version 1.11 of 31 December 2020
  Projection of failure_detectors:
  
  process (F \in failure_detectors)
  {
    par {
      all (p \in participants) {
        either {
          await voted_no \/ some_failed;
        } or {
          await voted_yes = participants;
        }
      }
    } and {
      all (p \in participants) {
        all (q \in participants \ { p }) {
          Send(self, p, << "failed" , q >>);
        }
      }
    }
  }
  
  Projection of participants:
  
  process (P \in participants)
    variables
      voted_yes = { };
      voted_no = FALSE;
      outcome = "none";
  {
    par {
      task P, "votes" {
        par {
          par {
            either {
              Send(self, self, "yes");
              Receive(self, self, "yes");
              voted_yes := voted_yes \cup { self };
            } or {
              Send(self, self, "no");
              Receive(self, self, "no");
              voted_no := TRUE;
            }
          } and {
            all (q \in participants \ { self }) {
              either {
                Send(self, q, "yes");
              } or {
                Send(self, q, "no");
              }
            }
          }
        } and {
          all (p \in participants \ { self }) {
            either {
              Receive(p, self, "yes");
              voted_yes := voted_yes \cup { p };
            } or {
              Receive(p, self, "no");
              voted_no := TRUE;
            }
          }
        }
      }
    } and {
      task P, "votes" {
        par {
          par {
            either {
              Send(self, self, "yes");
              Receive(self, self, "yes");
              voted_yes := voted_yes \cup { self };
            } or {
              Send(self, self, "no");
              Receive(self, self, "no");
              voted_no := TRUE;
            }
          } and {
            all (q \in participants \ { self }) {
              either {
                Send(self, q, "yes");
              } or {
                Send(self, q, "no");
              }
            }
          }
        } and {
          all (p \in participants \ { self }) {
            either {
              Receive(p, self, "yes");
              voted_yes := voted_yes \cup { p };
            } or {
              Receive(p, self, "no");
              voted_no := TRUE;
            }
          }
        }
      }
    } and {
      all (f \in failure_detectors) {
        all (q \in participants \ { self }) {
          Receive(f, self, << "failed" , q >>);
        }
      }
    }
  }
  
  Final processes:
  
  process (F \in failure_detectors)
  {
    par_45:
    await \A v_50 \in ( { "F_par_46" , "F_par_48" } \X { failure_detectors } ) : pc [ v_50 ] = "Done";
  }
  process (P \in participants)
    variables
      voted_yes = { };
      voted_no = FALSE;
      outcome = "none";
  {
    par_0:
    await \A v_25 \in ( { "P_par_1" , "P_par_15" , "P_par_23" } \X { participants } ) : pc [ v_25 ] = "Done";
  }
  process (proc_10 \in ( "P_par_3" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_2";
    par_4:
    await \A v_9 \in ( { "P_par_5" , "P_par_7" } \X { participants } ) : pc [ v_9 ] = "Done";
  }
  process (proc_12 \in ( "P_par_11" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_2";
    fork_34:
    await \A p \in ( participants \ { Head ( Tail ( self ) ) } \X participants ) : pc [ p ] = "Done";
  }
  process (proc_14 \in ( "P_par_1" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    if (~ cancelled_votes) {
      par_2:
      await \A v_13 \in ( { "P_par_3" , "P_par_11" } \X { participants } ) : pc [ v_13 ] = "Done";
    } else {
      skip;
    }
  }
  process (proc_18 \in ( "P_par_17" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_16";
    either {
      await voted_no \/ some_failed;
      outcome := "abort";
    } or {
      await voted_yes = participants;
      outcome := "commit";
    }
  }
  process (proc_20 \in ( "P_par_19" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_16";
    fork_38:
    await \A p \in ( participants \ { Head ( Tail ( self ) ) } \X participants ) : pc [ p ] = "Done";
  }
  process (proc_22 \in ( "P_par_15" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    par_16:
    await \A v_21 \in ( { "P_par_17" , "P_par_19" } \X { participants } ) : pc [ v_21 ] = "Done";
  }
  process (proc_24 \in ( "P_par_23" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_0";
    fork_40:
    await \A f \in ( failure_detectors \X participants ) : pc [ f ] = "Done";
  }
  process (proc_31 \in ( participants \ { Head ( Tail ( self ) ) } \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_30";
    either {
      comm_32:
      Send(Head ( Tail ( self ) ), Head(self), "yes");
    } or {
      comm_33:
      Send(Head ( Tail ( self ) ), Head(self), "no");
    }
  }
  process (proc_35 \in ( participants \ { Head ( Tail ( self ) ) } \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_34";
    either {
      comm_36:
      Receive(Head(self), Head ( Tail ( self ) ), "yes");
      voted_yes := voted_yes \cup { Head(self) };
    } or {
      comm_37:
      Receive(Head(self), Head ( Tail ( self ) ), "no");
      voted_no := TRUE;
    }
  }
  process (proc_39 \in ( participants \ { Head ( Tail ( self ) ) } \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_38";
    either {
      await voted_no \/ some_failed;
    } or {
      await voted_yes = participants;
    }
  }
  process (proc_42 \in ( participants \ { Head ( Tail ( self ) ) } \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_41";
    comm_44:
    Receive(f, Head ( Tail ( self ) ), << "failed" , Head(self) >>);
  }
  process (proc_43 \in ( failure_detectors \X participants ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_40";
    fork_41:
    await \A q \in ( participants \ { Head ( Tail ( self ) ) } \X participants ) : pc [ q ] = "Done";
  }
  process (proc_47 \in ( "F_par_46" \X { failure_detectors } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_45";
    fork_51:
    await \A p \in ( participants \X failure_detectors ) : pc [ p ] = "Done";
  }
  process (proc_49 \in ( "F_par_48" \X { failure_detectors } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_45";
    fork_53:
    await \A p \in ( participants \X failure_detectors ) : pc [ p ] = "Done";
  }
  process (proc_52 \in ( participants \X failure_detectors ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_51";
    either {
      await voted_no \/ some_failed;
    } or {
      await voted_yes = participants;
    }
  }
  process (proc_55 \in ( participants \ { p } \X failure_detectors ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_54";
    comm_57:
    Send(Head ( Tail ( self ) ), p, << "failed" , Head(self) >>);
  }
  process (proc_56 \in ( participants \X failure_detectors ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "fork_53";
    fork_54:
    await \A q \in ( participants \ { Head(self) } \X failure_detectors ) : pc [ q ] = "Done";
  }
  process (proc_6 \in ( "P_par_5" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_4";
    either {
      comm_26:
      Send(Head(Tail(self)), Head(Tail(self)), "yes");
      comm_27:
      Receive(Head(Tail(self)), Head(Tail(self)), "yes");
      voted_yes := voted_yes \cup { Head(Tail(self)) };
    } or {
      comm_28:
      Send(Head(Tail(self)), Head(Tail(self)), "no");
      comm_29:
      Receive(Head(Tail(self)), Head(Tail(self)), "no");
      voted_no := TRUE;
    }
  }
  process (proc_8 \in ( "P_par_7" \X { participants } ))
  {
    await pc [ Head ( Tail ( self ) ) ] = "par_4";
    fork_30:
    await \A q \in ( participants \ { Head ( Tail ( self ) ) } \X participants ) : pc [ q ] = "Done";
  }
  Labels added.
  Parsing completed.
  Translation completed.
  New file NBAC.tla written.

$ cpluscal -nocfg Raft.tla
