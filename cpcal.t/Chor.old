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
      Send(coord, p, "prepare");
      committed := committed \union {<<p, coord>>};
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "2b5a45c2" /\ chksum(tla) = "bb44a8b9")
VARIABLES participants, messages, pc, committed

vars == << participants, messages, pc, committed >>

ProcSet == ((coord \X participants)) \cup {coord} \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ messages = {}
        (* Process P *)
        /\ committed = [self \in participants |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in (coord \X participants) -> "Lbl_1"
                                        [] self = coord -> "fork_0"
                                        [] self \in participants -> "Lbl_2"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(self)] = "fork_0"
               /\ messages' = (messages \union {[To |-> self, From |-> p, Type |-> "prepare"]})
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, committed >>

proc_1(self) == Lbl_1(self)

fork_0 == /\ pc[coord] = "fork_0"
          /\ \A p \in (coord \X participants) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![coord] = "Done"]
          /\ UNCHANGED << participants, messages, committed >>

C == fork_0

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ [To |-> self, From |-> coord, Type |-> "prepare"] \in messages
               /\ committed' = [committed EXCEPT ![self] = committed[self] \union {<<p, coord>>}]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, messages >>

P(self) == Lbl_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in (coord \X participants): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
