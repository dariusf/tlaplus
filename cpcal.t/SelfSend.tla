--------------------- MODULE SelfSend ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm SelfSend {
  variables
    ps = {p1, p2};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (P \in participants);
  {
    all (p \in participants) {
      all (q \in participants \ {p}) {
        Transmit(p, q, "prepare");
      }
    }
  }


  choreography
    (P1 \in ps),
    (Q \in qs);
  {
    all (p \in ps) {
      all (q \in qs) {
        Transmit(p, q, "prepare");
      }
    }
  }

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "246ea10" /\ chksum(tla) = "e7db024d")
VARIABLES ps, messages, pc

vars == << ps, messages, pc >>

ProcSet == ((participants \X {"P_par_5"})) \cup ((participants \X participants \ { p , self })) \cup ((participants \X {"P_par_7"})) \cup ((participants \X participants \ { self })) \cup ((participants \X {"P_par_1"})) \cup ((participants \X participants \ { self })) \cup ((participants \X {"P_par_3"})) \cup (participants)

Init == (* Global variables *)
        /\ ps = {p1, p2}
        /\ messages = {}
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X {"P_par_5"}) -> "Lbl_1"
                                        [] self \in (participants \X participants \ { p , self }) -> "Lbl_2"
                                        [] self \in (participants \X {"P_par_7"}) -> "Lbl_3"
                                        [] self \in (participants \X participants \ { self }) -> "Lbl_4"
                                        [] self \in (participants \X {"P_par_1"}) -> "Lbl_5"
                                        [] self \in (participants \X participants \ { self }) -> "Lbl_6"
                                        [] self \in (participants \X {"P_par_3"}) -> "Lbl_7"
                                        [] self \in participants -> "par_0"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(self)] = "par_4"
               /\ [To |-> self, From |-> p, Type |-> "prepare"] \in messages
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << ps, messages >>

proc_6(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(self)] = "fork_12"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << ps, messages >>

proc_13(self) == Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(self)] = "par_4"
               /\ pc' = [pc EXCEPT ![self] = "fork_12"]
               /\ UNCHANGED << ps, messages >>

fork_12(self) == /\ pc[self] = "fork_12"
                 /\ \A q \in (participants \X participants \ { p , self }) : pc[q] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ps, messages >>

proc_8(self) == Lbl_3(self) \/ fork_12(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Head(self)] = "fork_14"
               /\ messages' = (messages \union {[To |-> q, From |-> self, Type |-> "prepare"]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ ps' = ps

proc_15(self) == Lbl_4(self)

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ pc[Head(self)] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "fork_14"]
               /\ UNCHANGED << ps, messages >>

fork_14(self) == /\ pc[self] = "fork_14"
                 /\ \A q \in (participants \X participants \ { self }) : pc[q] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ps, messages >>

proc_2(self) == Lbl_5(self) \/ fork_14(self)

Lbl_6(self) == /\ pc[self] = "Lbl_6"
               /\ pc[Head(self)] = "fork_16"
               /\ pc' = [pc EXCEPT ![self] = "par_4"]
               /\ UNCHANGED << ps, messages >>

par_4(self) == /\ pc[self] = "par_4"
               /\ \A v_9 \in (participants \X {"P_par_5", "P_par_7"}) : pc[v_9] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << ps, messages >>

proc_17(self) == Lbl_6(self) \/ par_4(self)

Lbl_7(self) == /\ pc[self] = "Lbl_7"
               /\ pc[Head(self)] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "fork_16"]
               /\ UNCHANGED << ps, messages >>

fork_16(self) == /\ pc[self] = "fork_16"
                 /\ \A p \in (participants \X participants \ { self }) : pc[p] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ps, messages >>

proc_10(self) == Lbl_7(self) \/ fork_16(self)

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_11 \in (participants \X {"P_par_1", "P_par_3"}) : pc[v_11] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << ps, messages >>

P(self) == par_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (participants \X {"P_par_5"}): proc_6(self))
           \/ (\E self \in (participants \X participants \ { p , self }): proc_13(self))
           \/ (\E self \in (participants \X {"P_par_7"}): proc_8(self))
           \/ (\E self \in (participants \X participants \ { self }): proc_15(self))
           \/ (\E self \in (participants \X {"P_par_1"}): proc_2(self))
           \/ (\E self \in (participants \X participants \ { self }): proc_17(self))
           \/ (\E self \in (participants \X {"P_par_3"}): proc_10(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
