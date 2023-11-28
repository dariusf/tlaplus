--------------------- MODULE Chor ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm Chor {
  variables
    participants = {p1, p2};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (C = coord),
    (P \in participants)
      variables
        committed = {};
  {
    all (p \in participants) {
      Transmit(coord, p, "prepare");
      committed := committed \union {<<p, coord>>};
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "b3daf4a7" /\ chksum(tla) = "ce46790")
VARIABLES participants, messages, pc, committed

vars == << participants, messages, pc, committed >>

ProcSet == {coord} \cup ((participants \X {"P_par_1"})) \cup ((participants \X participants \ { self })) \cup ((participants \X {"P_par_3"})) \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ messages = {}
        (* Process P *)
        /\ committed = [self \in participants |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = coord -> "Lbl_1"
                                        [] self \in (participants \X {"P_par_1"}) -> "Lbl_2"
                                        [] self \in (participants \X participants \ { self }) -> "Lbl_3"
                                        [] self \in (participants \X {"P_par_3"}) -> "Lbl_4"
                                        [] self \in participants -> "par_0"]

Lbl_1 == /\ pc[coord] = "Lbl_1"
         /\ TRUE
         /\ pc' = [pc EXCEPT ![coord] = "Done"]
         /\ UNCHANGED << participants, messages, committed >>

C == Lbl_1

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(self)] = "par_0"
               /\ [To |-> self, From |-> coord, Type |-> "prepare"] \in messages
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, messages, committed >>

proc_2(self) == Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(self)] = "fork_6"
               /\ committed' = [committed EXCEPT ![self] = committed[self] \union {<<p, coord>>}]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, messages >>

proc_7(self) == Lbl_3(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Head(self)] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "fork_6"]
               /\ UNCHANGED << participants, messages, committed >>

fork_6(self) == /\ pc[self] = "fork_6"
                /\ \A p \in (participants \X participants \ { self }) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, messages, committed >>

proc_4(self) == Lbl_4(self) \/ fork_6(self)

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_5 \in (participants \X {"P_par_1", "P_par_3"}) : pc[v_5] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, messages, committed >>

P(self) == par_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in (participants \X {"P_par_1"}): proc_2(self))
           \/ (\E self \in (participants \X participants \ { self }): proc_7(self))
           \/ (\E self \in (participants \X {"P_par_3"}): proc_4(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
