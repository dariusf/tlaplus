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
\* BEGIN TRANSLATION (chksum(pcal) = "2dc50475" /\ chksum(tla) = "b43d6e68")
VARIABLES ps, messages, pc

vars == << ps, messages, pc >>

ProcSet == ((participants \ { Tail(self) } \X participants)) \cup (participants) \cup ((ps \X qs)) \cup (qs) \cup ((qs \X ps)) \cup (ps)

Init == (* Global variables *)
        /\ ps = {p1, p2}
        /\ messages = {}
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \ { Tail(self) } \X participants) -> "Lbl_1"
                                        [] self \in participants -> "fork_0"
                                        [] self \in (ps \X qs) -> "Lbl_2"
                                        [] self \in qs -> "fork_2"
                                        [] self \in (qs \X ps) -> "Lbl_3"
                                        [] self \in ps -> "fork_4"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Tail(self)] = "fork_0"
               /\ messages' = (messages \union {[To |-> Head(self), From |-> (Tail(self)), Type |-> prepare]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ ps' = ps

proc_1(self) == Lbl_1(self)

fork_0(self) == /\ pc[self] = "fork_0"
                /\ \A q \in (participants \ { Tail(self) } \X participants) : pc[q] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

P(self) == fork_0(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Tail(self)] = "fork_2"
               /\ [To |-> (Tail(self)), From |-> Head(self), Type |-> prepare] \in messages
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << ps, messages >>

proc_3(self) == Lbl_2(self)

fork_2(self) == /\ pc[self] = "fork_2"
                /\ \A p \in (ps \X qs) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

Q(self) == fork_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Tail(self)] = "fork_4"
               /\ messages' = (messages \union {[To |-> Head(self), From |-> (Tail(self)), Type |-> prepare]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ ps' = ps

proc_5(self) == Lbl_3(self)

fork_4(self) == /\ pc[self] = "fork_4"
                /\ \A q \in (qs \X ps) : pc[q] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

P1(self) == fork_4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (participants \ { Tail(self) } \X participants): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (ps \X qs): proc_3(self))
           \/ (\E self \in qs: Q(self))
           \/ (\E self \in (qs \X ps): proc_5(self))
           \/ (\E self \in ps: P1(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
