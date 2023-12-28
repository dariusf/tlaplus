--------------------- MODULE Assign ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, c1, c2

(* --algorithm Assign {
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
    (P \in participants)
      variables
        committed = {};
  {
    all (c \in coordinators) {
      all (p \in participants) {
        committed := committed \union {<<p, c>>};
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "6e345ada" /\ chksum(tla) = "1e7e408f")
VARIABLES participants, coordinators, messages, pc, committed

vars == << participants, coordinators, messages, pc, committed >>

ProcSet == ((coordinators \X participants)) \cup (participants) \cup (coordinators)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c1, c2}
        /\ messages = {}
        (* Process P *)
        /\ committed = [self \in participants |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in (coordinators \X participants) -> "Lbl_1"
                                        [] self \in participants -> "fork_0"
                                        [] self \in coordinators -> "Lbl_2"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "fork_0"
               /\ committed' = [committed EXCEPT ![self] = committed[self] \union { << Head(Tail(self)) , Head(self)>> }]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages >>

proc_1(self) == Lbl_1(self)

fork_0(self) == /\ pc[self] = "fork_0"
                /\ \A c \in (coordinators \X participants) : pc[c] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, messages, 
                                committed >>

P(self) == fork_0(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages, committed >>

C(self) == Lbl_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (coordinators \X participants): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ (\E self \in coordinators: C(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
