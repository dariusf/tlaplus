--------------------- MODULE TwoPhaseCommit ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, c

(* --algorithm TwoPhaseCommit {
  variables
    participants = {p1, p2};
    coordinators = {c};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (C \in coordinators);
    (P \in participants);
  {
    all (c \in coordinators) {
      task C, "phase1" {
        all (p \in participants) {
          Transmit(c, p, "prepare");
          either {
            Transmit(p, c, "prepared");
          } or {
            Transmit(p, c, "aborted");
            cancel "phase1";
          }
        }
      };
      if (aborted) {
        all (p \in participants) {
          Transmit(c, p, "abort");
          Transmit(p, c, "aborted");
        }
      } else {
        all (p \in participants) {
          Transmit(c, p, "commit");
          Transmit(p, c, "committed");
        }
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "f1df6890" /\ chksum(tla) = "d0431cd8")
VARIABLES participants, coordinators, messages, cancelled_phase1, pc

vars == << participants, coordinators, messages, cancelled_phase1, pc >>

ProcSet == ((participants \X coordinators)) \cup ((participants \X coordinators)) \cup ((participants \X coordinators)) \cup (("C_par_1" \X {coordinators})) \cup ((coordinators \ { Head(Tail(self)) } \X coordinators)) \cup (("C_par_3" \X {coordinators})) \cup (coordinators) \cup ((coordinators \X participants)) \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c}
        /\ messages = {}
        /\ cancelled_phase1 = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X coordinators) -> "Lbl_1"
                                        [] self \in (participants \X coordinators) -> "Lbl_2"
                                        [] self \in (participants \X coordinators) -> "Lbl_3"
                                        [] self \in ("C_par_1" \X {coordinators}) -> "Lbl_4"
                                        [] self \in (coordinators \ { Head(Tail(self)) } \X coordinators) -> "Lbl_6"
                                        [] self \in ("C_par_3" \X {coordinators}) -> "Lbl_7"
                                        [] self \in coordinators -> "par_0"
                                        [] self \in (coordinators \X participants) -> "Lbl_8"
                                        [] self \in participants -> "fork_21"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "fork_6"
               /\ pc' = [pc EXCEPT ![self] = "comm_12"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

comm_12(self) == /\ pc[self] = "comm_12"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "prepare"]})
                 /\ \/ /\ pc' = [pc EXCEPT ![self] = "comm_13"]
                    \/ /\ pc' = [pc EXCEPT ![self] = "comm_14"]
                 /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

comm_13(self) == /\ pc[self] = "comm_13"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "prepared"] \in messages
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

comm_14(self) == /\ pc[self] = "comm_14"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "aborted"] \in messages
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

proc_7(self) == Lbl_1(self) \/ comm_12(self) \/ comm_13(self)
                   \/ comm_14(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(Tail(self))] = "fork_8"
               /\ pc' = [pc EXCEPT ![self] = "comm_15"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

comm_15(self) == /\ pc[self] = "comm_15"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "abort"]})
                 /\ pc' = [pc EXCEPT ![self] = "comm_16"]
                 /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

comm_16(self) == /\ pc[self] = "comm_16"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "aborted"] \in messages
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

proc_9(self) == Lbl_2(self) \/ comm_15(self) \/ comm_16(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(Tail(self))] = "fork_10"
               /\ pc' = [pc EXCEPT ![self] = "comm_17"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

comm_17(self) == /\ pc[self] = "comm_17"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "commit"]})
                 /\ pc' = [pc EXCEPT ![self] = "comm_18"]
                 /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

comm_18(self) == /\ pc[self] = "comm_18"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "committed"] \in messages
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

proc_11(self) == Lbl_3(self) \/ comm_17(self) \/ comm_18(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Head(Tail(self))] = "par_0"
               /\ IF ~ cancelled_phase1
                     THEN /\ pc' = [pc EXCEPT ![self] = "fork_6"]
                     ELSE /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_5"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

fork_6(self) == /\ pc[self] = "fork_6"
                /\ \A p \in (participants \X coordinators) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Lbl_5"]
                /\ UNCHANGED << participants, coordinators, messages, 
                                cancelled_phase1 >>

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ IF aborted
                     THEN /\ pc' = [pc EXCEPT ![self] = "fork_8"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "fork_10"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

fork_8(self) == /\ pc[self] = "fork_8"
                /\ \A p \in (participants \X coordinators) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, messages, 
                                cancelled_phase1 >>

fork_10(self) == /\ pc[self] = "fork_10"
                 /\ \A p \in (participants \X coordinators) : pc[p] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

proc_2(self) == Lbl_4(self) \/ fork_6(self) \/ Lbl_5(self) \/ fork_8(self)
                   \/ fork_10(self)

Lbl_6(self) == /\ pc[self] = "Lbl_6"
               /\ pc[Head(Tail(self))] = "fork_19"
               /\ IF aborted
                     THEN /\ TRUE
                     ELSE /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

proc_20(self) == Lbl_6(self)

Lbl_7(self) == /\ pc[self] = "Lbl_7"
               /\ pc[Head(Tail(self))] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "fork_19"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

fork_19(self) == /\ pc[self] = "fork_19"
                 /\ \A c \in (coordinators \ { Head(Tail(self)) } \X coordinators) : pc[c] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

proc_4(self) == Lbl_7(self) \/ fork_19(self)

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_5 \in ({"C_par_1", "C_par_3"} \X {coordinators}) : pc[v_5] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

C(self) == par_0(self)

Lbl_8(self) == /\ pc[self] = "Lbl_8"
               /\ pc[Head(Tail(self))] = "fork_21"
               /\ pc' = [pc EXCEPT ![self] = "comm_23"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

comm_23(self) == /\ pc[self] = "comm_23"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "prepare"] \in messages
                 /\ \/ /\ pc' = [pc EXCEPT ![self] = "comm_24"]
                    \/ /\ pc' = [pc EXCEPT ![self] = "comm_25"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

comm_24(self) == /\ pc[self] = "comm_24"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "prepared"]})
                 /\ pc' = [pc EXCEPT ![self] = "Lbl_9"]
                 /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

comm_25(self) == /\ pc[self] = "comm_25"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "aborted"]})
                 /\ pc' = [pc EXCEPT ![self] = "Lbl_9"]
                 /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

Lbl_9(self) == /\ pc[self] = "Lbl_9"
               /\ IF aborted
                     THEN /\ pc' = [pc EXCEPT ![self] = "comm_26"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "comm_28"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

comm_26(self) == /\ pc[self] = "comm_26"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "abort"] \in messages
                 /\ pc' = [pc EXCEPT ![self] = "comm_27"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

comm_27(self) == /\ pc[self] = "comm_27"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "aborted"]})
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

comm_28(self) == /\ pc[self] = "comm_28"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "commit"] \in messages
                 /\ pc' = [pc EXCEPT ![self] = "comm_29"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

comm_29(self) == /\ pc[self] = "comm_29"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "committed"]})
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

proc_22(self) == Lbl_8(self) \/ comm_23(self) \/ comm_24(self)
                    \/ comm_25(self) \/ Lbl_9(self) \/ comm_26(self)
                    \/ comm_27(self) \/ comm_28(self) \/ comm_29(self)

fork_21(self) == /\ pc[self] = "fork_21"
                 /\ \A c \in (coordinators \X participants) : pc[c] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages, 
                                 cancelled_phase1 >>

P(self) == fork_21(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (participants \X coordinators): proc_7(self))
           \/ (\E self \in (participants \X coordinators): proc_9(self))
           \/ (\E self \in (participants \X coordinators): proc_11(self))
           \/ (\E self \in ("C_par_1" \X {coordinators}): proc_2(self))
           \/ (\E self \in (coordinators \ { Head(Tail(self)) } \X coordinators): proc_20(self))
           \/ (\E self \in ("C_par_3" \X {coordinators}): proc_4(self))
           \/ (\E self \in coordinators: C(self))
           \/ (\E self \in (coordinators \X participants): proc_22(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
