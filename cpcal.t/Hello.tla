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
\* BEGIN TRANSLATION (chksum(pcal) = "ad591e52" /\ chksum(tla) = "edb8c7c0")
VARIABLES participants, coordinators, messages, pc

vars == << participants, coordinators, messages, pc >>

ProcSet == ((coordinators \X participants)) \cup (participants) \cup ((participants \X coordinators)) \cup (coordinators)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c1, c2}
        /\ messages = {}
        /\ pc = [self \in ProcSet |-> CASE self \in (coordinators \X participants) -> "Lbl_1"
                                        [] self \in participants -> "fork_0"
                                        [] self \in (participants \X coordinators) -> "Lbl_2"
                                        [] self \in coordinators -> "fork_2"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "fork_0"
               /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "a"] \in messages
               /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "b"]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators >>

proc_1(self) == Lbl_1(self)

fork_0(self) == /\ pc[self] = "fork_0"
                /\ \A c \in (coordinators \X participants) : pc[c] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, messages >>

P(self) == fork_0(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(Tail(self))] = "fork_2"
               /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "a"]})
               /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "b"] \in messages'
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators >>

proc_3(self) == Lbl_2(self)

fork_2(self) == /\ pc[self] = "fork_2"
                /\ \A p \in (participants \X coordinators) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, messages >>

C(self) == fork_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (coordinators \X participants): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (participants \X coordinators): proc_3(self))
           \/ (\E self \in coordinators: C(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
