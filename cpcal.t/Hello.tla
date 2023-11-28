--------------------- MODULE Hello ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, c1, c2

(* --algorithm Hello {
  variables
    participants = {p1, p2};
    coordinators = {c1, c2};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (C \in coordinators),
    (P \in participants);
  {
    all (c \in coordinators) {
      all (p \in participants) {
        Transmit(c, p, "a");
        Transmit(p, c, "b");
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "a7fddb4a" /\ chksum(tla) = "1d290692")
VARIABLES participants, coordinators, messages, pc

vars == << participants, coordinators, messages, pc >>

ProcSet == ((participants \X {"P_par_1"})) \cup ((participants \X participants \ { self })) \cup ((participants \X {"P_par_3"})) \cup ((participants \X coordinators)) \cup (participants) \cup ((coordinators \X participants)) \cup ((coordinators \X {"C_par_11"})) \cup ((coordinators \X participants)) \cup ((coordinators \X coordinators \ { self })) \cup ((coordinators \X {"C_par_13"})) \cup (coordinators)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c1, c2}
        /\ messages = {}
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X {"P_par_1"}) -> "Lbl_1"
                                        [] self \in (participants \X participants \ { self }) -> "Lbl_2"
                                        [] self \in (participants \X {"P_par_3"}) -> "Lbl_3"
                                        [] self \in (participants \X coordinators) -> "Lbl_4"
                                        [] self \in participants -> "fork_8"
                                        [] self \in (coordinators \X participants) -> "Lbl_5"
                                        [] self \in (coordinators \X {"C_par_11"}) -> "Lbl_6"
                                        [] self \in (coordinators \X participants) -> "Lbl_7"
                                        [] self \in (coordinators \X coordinators \ { self }) -> "Lbl_8"
                                        [] self \in (coordinators \X {"C_par_13"}) -> "Lbl_9"
                                        [] self \in coordinators -> "par_10"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(self)] = "par_0"
               /\ [To |-> self, From |-> c, Type |-> "a"] \in messages
               /\ messages' = (messages \union {[To |-> c, From |-> self, Type |-> "b"]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators >>

proc_2(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(self)] = "fork_6"
               /\ TRUE
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages >>

proc_7(self) == Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(self)] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "fork_6"]
               /\ UNCHANGED << participants, coordinators, messages >>

fork_6(self) == /\ pc[self] = "fork_6"
                /\ \A p \in (participants \X participants \ { self }) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, messages >>

proc_4(self) == Lbl_3(self) \/ fork_6(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Head(self)] = "fork_8"
               /\ pc' = [pc EXCEPT ![self] = "par_0"]
               /\ UNCHANGED << participants, coordinators, messages >>

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_5 \in (participants \X {"P_par_1", "P_par_3"}) : pc[v_5] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages >>

proc_9(self) == Lbl_4(self) \/ par_0(self)

fork_8(self) == /\ pc[self] = "fork_8"
                /\ \A c \in (participants \X coordinators) : pc[c] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, messages >>

P(self) == fork_8(self)

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ pc[Head(self)] = "fork_16"
               /\ messages' = (messages \union {[To |-> p, From |-> self, Type |-> "a"]})
               /\ [To |-> self, From |-> p, Type |-> "b"] \in messages'
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators >>

proc_17(self) == Lbl_5(self)

Lbl_6(self) == /\ pc[self] = "Lbl_6"
               /\ pc[Head(self)] = "par_10"
               /\ pc' = [pc EXCEPT ![self] = "fork_16"]
               /\ UNCHANGED << participants, coordinators, messages >>

fork_16(self) == /\ pc[self] = "fork_16"
                 /\ \A p \in (coordinators \X participants) : pc[p] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages >>

proc_12(self) == Lbl_6(self) \/ fork_16(self)

Lbl_7(self) == /\ pc[self] = "Lbl_7"
               /\ pc[Head(self)] = "fork_19"
               /\ TRUE
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages >>

proc_20(self) == Lbl_7(self)

Lbl_8(self) == /\ pc[self] = "Lbl_8"
               /\ pc[Head(self)] = "fork_18"
               /\ pc' = [pc EXCEPT ![self] = "fork_19"]
               /\ UNCHANGED << participants, coordinators, messages >>

fork_19(self) == /\ pc[self] = "fork_19"
                 /\ \A p \in (coordinators \X participants) : pc[p] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages >>

proc_21(self) == Lbl_8(self) \/ fork_19(self)

Lbl_9(self) == /\ pc[self] = "Lbl_9"
               /\ pc[Head(self)] = "par_10"
               /\ pc' = [pc EXCEPT ![self] = "fork_18"]
               /\ UNCHANGED << participants, coordinators, messages >>

fork_18(self) == /\ pc[self] = "fork_18"
                 /\ \A c \in (coordinators \X coordinators \ { self }) : pc[c] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << participants, coordinators, messages >>

proc_14(self) == Lbl_9(self) \/ fork_18(self)

par_10(self) == /\ pc[self] = "par_10"
                /\ \A v_15 \in (coordinators \X {"C_par_11", "C_par_13"}) : pc[v_15] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, messages >>

C(self) == par_10(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (participants \X {"P_par_1"}): proc_2(self))
           \/ (\E self \in (participants \X participants \ { self }): proc_7(self))
           \/ (\E self \in (participants \X {"P_par_3"}): proc_4(self))
           \/ (\E self \in (participants \X coordinators): proc_9(self))
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (coordinators \X participants): proc_17(self))
           \/ (\E self \in (coordinators \X {"C_par_11"}): proc_12(self))
           \/ (\E self \in (coordinators \X participants): proc_20(self))
           \/ (\E self \in (coordinators \X coordinators \ { self }): proc_21(self))
           \/ (\E self \in (coordinators \X {"C_par_13"}): proc_14(self))
           \/ (\E self \in coordinators: C(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
