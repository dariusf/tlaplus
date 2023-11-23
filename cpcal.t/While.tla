--------------------- MODULE While ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm While {
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
    (C = coord)
      variables y = 3,
    (P \in participants)
      variables x = 1;
  {
    all (p \in participants) {
      while (y > 1), (x < 3) {
        Send(coord, p, 5);
        y := y - 1;
        x := x + 1;
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "43018a82" /\ chksum(tla) = "9a0afb90")
VARIABLES participants, messages, pc, x, y

vars == << participants, messages, pc, x, y >>

ProcSet == (participants) \cup ((coord \X participants)) \cup {coord}

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ messages = {}
        (* Process P *)
        /\ x = [self \in participants |-> 1]
        (* Process C *)
        /\ y = 3
        /\ pc = [self \in ProcSet |-> CASE self \in participants -> "Lbl_1"
                                        [] self \in (coord \X participants) -> "Lbl_2"
                                        [] self = coord -> "fork_0"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ IF x[self] < 3
                     THEN /\ [To |-> self, From |-> coord, Type |-> 5] \in messages
                          /\ TRUE
                          /\ x' = [x EXCEPT ![self] = x[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_1"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ x' = x
               /\ UNCHANGED << participants, messages, y >>

P(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(self)] = "fork_0"
               /\ pc' = [pc EXCEPT ![self] = "Lbl_3"]
               /\ UNCHANGED << participants, messages, x, y >>

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ IF y > 1
                     THEN /\ messages' = (messages \union {[To |-> self, From |-> p, Type |-> 5]})
                          /\ y' = y - 1
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << messages, y >>
               /\ UNCHANGED << participants, x >>

proc_1(self) == Lbl_2(self) \/ Lbl_3(self)

fork_0 == /\ pc[coord] = "fork_0"
          /\ \A p \in (coord \X participants) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![coord] = "Done"]
          /\ UNCHANGED << participants, messages, x, y >>

C == fork_0

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (coord \X participants): proc_1(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
