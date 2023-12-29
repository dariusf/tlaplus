--------------------- MODULE NBAC ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, f

(* --algorithm NBAC {
  variables
    participants = {p1, p2};
    failure_detectors = {f};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (F \in failure_detectors),
    (P \in participants)
    variables
      voted_yes = {},
      voted_no = FALSE,
      outcome = "none";
  {
    par {
      task P, "votes" {
        all (p \in participants) {
          all (q \in participants) {
            either {
              Transmit(p, q, "yes");
              voted_yes[q] := voted_yes[q] \cup {p};
            } or {
              Transmit(p, q, "no");
              voted_no[q] := TRUE;
              cancel "votes" q;
            }
          }
        }
      }
    } and {
      all (p \in participants) {
        either {
          await voted_no \/ some_failed; \* ?
          outcome := "abort";
        } or {
          await voted_yes = participants;
          outcome := "commit";
        }
      }
    } and {
      all (f \in failure_detectors) {
        all (p \in participants) {
          all (q \in participants \ {p}) {
            Transmit(f, p, <<"failed", q>>);
            some_failed[p] := TRUE;
          }
        }
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "de4460ef" /\ chksum(tla) = "16cf11a8")
VARIABLES participants, failure_detectors, messages, cancelled_votes, pc, 
          voted_yes, voted_no, outcome

vars == << participants, failure_detectors, messages, cancelled_votes, pc, 
           voted_yes, voted_no, outcome >>

ProcSet == ((participants \X failure_detectors)) \cup (("F_par_1" \X {failure_detectors})) \cup ((participants \ { p } \X failure_detectors)) \cup ((participants \X failure_detectors)) \cup (("F_par_3" \X {failure_detectors})) \cup (failure_detectors) \cup (("P_par_18" \X {participants})) \cup ((participants \ { Head(Tail(self)) } \X participants)) \cup (("P_par_20" \X {participants})) \cup (("P_par_16" \X {participants})) \cup ((participants \ { Head(Tail(self)) } \X participants)) \cup (("P_par_24" \X {participants})) \cup (("P_par_30" \X {participants})) \cup ((participants \ { Head(Tail(self)) } \X participants)) \cup (("P_par_32" \X {participants})) \cup (("P_par_14" \X {participants})) \cup (("P_par_28" \X {participants})) \cup ((participants \ { Head(Tail(self)) } \X participants)) \cup ((failure_detectors \X participants)) \cup (("P_par_36" \X {participants})) \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ failure_detectors = {f}
        /\ messages = {}
        /\ cancelled_votes = FALSE
        (* Process P *)
        /\ voted_yes = [self \in participants |-> {}]
        /\ voted_no = [self \in participants |-> FALSE]
        /\ outcome = [self \in participants |-> "none"]
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X failure_detectors) -> "Lbl_1"
                                        [] self \in ("F_par_1" \X {failure_detectors}) -> "Lbl_2"
                                        [] self \in (participants \ { p } \X failure_detectors) -> "Lbl_3"
                                        [] self \in (participants \X failure_detectors) -> "Lbl_4"
                                        [] self \in ("F_par_3" \X {failure_detectors}) -> "Lbl_5"
                                        [] self \in failure_detectors -> "par_0"
                                        [] self \in ("P_par_18" \X {participants}) -> "Lbl_6"
                                        [] self \in (participants \ { Head(Tail(self)) } \X participants) -> "Lbl_7"
                                        [] self \in ("P_par_20" \X {participants}) -> "Lbl_8"
                                        [] self \in ("P_par_16" \X {participants}) -> "Lbl_9"
                                        [] self \in (participants \ { Head(Tail(self)) } \X participants) -> "Lbl_10"
                                        [] self \in ("P_par_24" \X {participants}) -> "Lbl_11"
                                        [] self \in ("P_par_30" \X {participants}) -> "Lbl_12"
                                        [] self \in (participants \ { Head(Tail(self)) } \X participants) -> "Lbl_13"
                                        [] self \in ("P_par_32" \X {participants}) -> "Lbl_14"
                                        [] self \in ("P_par_14" \X {participants}) -> "Lbl_15"
                                        [] self \in ("P_par_28" \X {participants}) -> "Lbl_16"
                                        [] self \in (participants \ { Head(Tail(self)) } \X participants) -> "Lbl_17"
                                        [] self \in (failure_detectors \X participants) -> "Lbl_18"
                                        [] self \in ("P_par_36" \X {participants}) -> "Lbl_19"
                                        [] self \in participants -> "par_13"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "fork_6"
               /\ \/ /\ voted_no[self] \/ some_failed
                  \/ /\ voted_yes[self] = participants
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

proc_7(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(Tail(self))] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "fork_6"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

fork_6(self) == /\ pc[self] = "fork_6"
                /\ \A p \in (participants \X failure_detectors) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

proc_2(self) == Lbl_2(self) \/ fork_6(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(Tail(self))] = "fork_9"
               /\ pc' = [pc EXCEPT ![self] = "comm_12"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

comm_12(self) == /\ pc[self] = "comm_12"
                 /\ messages' = (messages \union {[To |-> p, From |-> (Head(Tail(self))), Type |-> (<< "failed" , Head(self)>>)]})
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

proc_10(self) == Lbl_3(self) \/ comm_12(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Head(Tail(self))] = "fork_8"
               /\ pc' = [pc EXCEPT ![self] = "fork_9"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

fork_9(self) == /\ pc[self] = "fork_9"
                /\ \A q \in ( participants \ { Head(self)} \X failure_detectors ) : pc [ q ] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

proc_11(self) == Lbl_4(self) \/ fork_9(self)

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ pc[Head(Tail(self))] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "fork_8"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

fork_8(self) == /\ pc[self] = "fork_8"
                /\ \A p \in (participants \X failure_detectors) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

proc_4(self) == Lbl_5(self) \/ fork_8(self)

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_5 \in ({"F_par_1", "F_par_3"} \X {failure_detectors}) : pc[v_5] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

F(self) == par_0(self)

Lbl_6(self) == /\ pc[self] = "Lbl_6"
               /\ pc[Head(Tail(self))] = "par_17"
               /\ \/ /\ pc' = [pc EXCEPT ![self] = "comm_39"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "comm_41"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

comm_39(self) == /\ pc[self] = "comm_39"
                 /\ messages' = (messages \union {[To |-> Head(Tail(self)), From |-> Head(Tail(self)), Type |-> "yes"]})
                 /\ pc' = [pc EXCEPT ![self] = "comm_40"]
                 /\ UNCHANGED << participants, failure_detectors, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

comm_40(self) == /\ pc[self] = "comm_40"
                 /\ [To |-> Head(Tail(self)), From |-> Head(Tail(self)), Type |-> "yes"] \in messages
                 /\ voted_yes' = [voted_yes EXCEPT ![self] = voted_yes[self] \cup { Head(Tail(self))}]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_no, outcome >>

comm_41(self) == /\ pc[self] = "comm_41"
                 /\ messages' = (messages \union {[To |-> Head(Tail(self)), From |-> Head(Tail(self)), Type |-> "no"]})
                 /\ pc' = [pc EXCEPT ![self] = "comm_42"]
                 /\ UNCHANGED << participants, failure_detectors, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

comm_42(self) == /\ pc[self] = "comm_42"
                 /\ [To |-> Head(Tail(self)), From |-> Head(Tail(self)), Type |-> "no"] \in messages
                 /\ voted_no' = [voted_no EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_yes, outcome >>

proc_19(self) == Lbl_6(self) \/ comm_39(self) \/ comm_40(self)
                    \/ comm_41(self) \/ comm_42(self)

Lbl_7(self) == /\ pc[self] = "Lbl_7"
               /\ pc[Head(Tail(self))] = "fork_43"
               /\ \/ /\ pc' = [pc EXCEPT ![self] = "comm_45"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "comm_46"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

comm_45(self) == /\ pc[self] = "comm_45"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "yes"]})
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

comm_46(self) == /\ pc[self] = "comm_46"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "no"]})
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

proc_44(self) == Lbl_7(self) \/ comm_45(self) \/ comm_46(self)

Lbl_8(self) == /\ pc[self] = "Lbl_8"
               /\ pc[Head(Tail(self))] = "par_17"
               /\ pc' = [pc EXCEPT ![self] = "fork_43"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

fork_43(self) == /\ pc[self] = "fork_43"
                 /\ \A q \in (participants \ { Head(Tail(self)) } \X participants) : pc[q] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

proc_21(self) == Lbl_8(self) \/ fork_43(self)

Lbl_9(self) == /\ pc[self] = "Lbl_9"
               /\ pc[Head(Tail(self))] = "par_15"
               /\ pc' = [pc EXCEPT ![self] = "par_17"]
               /\ UNCHANGED << participants, failure_detectors, messages, 
                               cancelled_votes, voted_yes, voted_no, outcome >>

par_17(self) == /\ pc[self] = "par_17"
                /\ \A v_22 \in ({"P_par_18", "P_par_20"} \X {participants}) : pc[v_22] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

proc_23(self) == Lbl_9(self) \/ par_17(self)

Lbl_10(self) == /\ pc[self] = "Lbl_10"
                /\ pc[Head(Tail(self))] = "fork_47"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "comm_49"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "comm_50"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

comm_49(self) == /\ pc[self] = "comm_49"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "yes"] \in messages
                 /\ voted_yes' = [voted_yes EXCEPT ![self] = voted_yes[self] \cup { Head(self)}]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_no, outcome >>

comm_50(self) == /\ pc[self] = "comm_50"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "no"] \in messages
                 /\ voted_no' = [voted_no EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_yes, outcome >>

proc_48(self) == Lbl_10(self) \/ comm_49(self) \/ comm_50(self)

Lbl_11(self) == /\ pc[self] = "Lbl_11"
                /\ pc[Head(Tail(self))] = "par_15"
                /\ pc' = [pc EXCEPT ![self] = "fork_47"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

fork_47(self) == /\ pc[self] = "fork_47"
                 /\ \A p \in (participants \ { Head(Tail(self)) } \X participants) : pc[p] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

proc_25(self) == Lbl_11(self) \/ fork_47(self)

Lbl_12(self) == /\ pc[self] = "Lbl_12"
                /\ pc[Head(Tail(self))] = "par_29"
                /\ \/ /\ voted_no[self] \/ some_failed
                      /\ outcome' = [outcome EXCEPT ![self] = "abort"]
                   \/ /\ voted_yes[self] = participants
                      /\ outcome' = [outcome EXCEPT ![self] = "commit"]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no >>

proc_31(self) == Lbl_12(self)

Lbl_13(self) == /\ pc[self] = "Lbl_13"
                /\ pc[Head(Tail(self))] = "fork_51"
                /\ \/ /\ voted_no[self] \/ some_failed
                   \/ /\ voted_yes[self] = participants
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

proc_52(self) == Lbl_13(self)

Lbl_14(self) == /\ pc[self] = "Lbl_14"
                /\ pc[Head(Tail(self))] = "par_29"
                /\ pc' = [pc EXCEPT ![self] = "fork_51"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

fork_51(self) == /\ pc[self] = "fork_51"
                 /\ \A p \in (participants \ { Head(Tail(self)) } \X participants) : pc[p] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

proc_33(self) == Lbl_14(self) \/ fork_51(self)

Lbl_15(self) == /\ pc[self] = "Lbl_15"
                /\ pc[Head(Tail(self))] = "par_13"
                /\ IF ~ cancelled_votes
                      THEN /\ pc' = [pc EXCEPT ![self] = "par_15"]
                      ELSE /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

par_15(self) == /\ pc[self] = "par_15"
                /\ \A v_26 \in ({"P_par_16", "P_par_24"} \X {participants}) : pc[v_26] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

proc_27(self) == Lbl_15(self) \/ par_15(self)

Lbl_16(self) == /\ pc[self] = "Lbl_16"
                /\ pc[Head(Tail(self))] = "par_13"
                /\ pc' = [pc EXCEPT ![self] = "par_29"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

par_29(self) == /\ pc[self] = "par_29"
                /\ \A v_34 \in ({"P_par_30", "P_par_32"} \X {participants}) : pc[v_34] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

proc_35(self) == Lbl_16(self) \/ par_29(self)

Lbl_17(self) == /\ pc[self] = "Lbl_17"
                /\ pc[Head(Tail(self))] = "fork_54"
                /\ pc' = [pc EXCEPT ![self] = "comm_57"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

comm_57(self) == /\ pc[self] = "comm_57"
                 /\ [To |-> (Head(Tail(self))), From |-> f, Type |-> (<< "failed" , Head(self)>>)] \in messages
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

proc_55(self) == Lbl_17(self) \/ comm_57(self)

Lbl_18(self) == /\ pc[self] = "Lbl_18"
                /\ pc[Head(Tail(self))] = "fork_53"
                /\ pc' = [pc EXCEPT ![self] = "fork_54"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

fork_54(self) == /\ pc[self] = "fork_54"
                 /\ \A q \in ( participants \ { Head ( Tail ( self ) ) } \X participants ) : pc [ q ] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

proc_56(self) == Lbl_18(self) \/ fork_54(self)

Lbl_19(self) == /\ pc[self] = "Lbl_19"
                /\ pc[Head(Tail(self))] = "par_13"
                /\ pc' = [pc EXCEPT ![self] = "fork_53"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

fork_53(self) == /\ pc[self] = "fork_53"
                 /\ \A f \in (failure_detectors \X participants) : pc[f] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, failure_detectors, messages, 
                                 cancelled_votes, voted_yes, voted_no, outcome >>

proc_37(self) == Lbl_19(self) \/ fork_53(self)

par_13(self) == /\ pc[self] = "par_13"
                /\ \A v_38 \in ({"P_par_14", "P_par_28", "P_par_36"} \X {participants}) : pc[v_38] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, failure_detectors, messages, 
                                cancelled_votes, voted_yes, voted_no, outcome >>

P(self) == par_13(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (participants \X failure_detectors): proc_7(self))
           \/ (\E self \in ("F_par_1" \X {failure_detectors}): proc_2(self))
           \/ (\E self \in (participants \ { p } \X failure_detectors): proc_10(self))
           \/ (\E self \in (participants \X failure_detectors): proc_11(self))
           \/ (\E self \in ("F_par_3" \X {failure_detectors}): proc_4(self))
           \/ (\E self \in failure_detectors: F(self))
           \/ (\E self \in ("P_par_18" \X {participants}): proc_19(self))
           \/ (\E self \in (participants \ { Head(Tail(self)) } \X participants): proc_44(self))
           \/ (\E self \in ("P_par_20" \X {participants}): proc_21(self))
           \/ (\E self \in ("P_par_16" \X {participants}): proc_23(self))
           \/ (\E self \in (participants \ { Head(Tail(self)) } \X participants): proc_48(self))
           \/ (\E self \in ("P_par_24" \X {participants}): proc_25(self))
           \/ (\E self \in ("P_par_30" \X {participants}): proc_31(self))
           \/ (\E self \in (participants \ { Head(Tail(self)) } \X participants): proc_52(self))
           \/ (\E self \in ("P_par_32" \X {participants}): proc_33(self))
           \/ (\E self \in ("P_par_14" \X {participants}): proc_27(self))
           \/ (\E self \in ("P_par_28" \X {participants}): proc_35(self))
           \/ (\E self \in (participants \ { Head(Tail(self)) } \X participants): proc_55(self))
           \/ (\E self \in (failure_detectors \X participants): proc_56(self))
           \/ (\E self \in ("P_par_36" \X {participants}): proc_37(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
