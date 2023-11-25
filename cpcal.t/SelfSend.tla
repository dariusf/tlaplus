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
\* BEGIN TRANSLATION (chksum(pcal) = "94a9e80" /\ chksum(tla) = "b6e5fee2")
VARIABLES ps, messages, pc

vars == << ps, messages, pc >>

ProcSet == ((participants \X participants \ { self })) \cup (participants) \cup ((qs \X ps)) \cup (qs) \cup ((ps \X qs)) \cup (ps)

Init == (* Global variables *)
        /\ ps = {p1, p2}
        /\ messages = {}
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X participants \ { self }) -> "Lbl_1"
                                        [] self \in participants -> "fork_0"
                                        [] self \in (qs \X ps) -> "Lbl_2"
                                        [] self \in qs -> "fork_2"
                                        [] self \in (ps \X qs) -> "Lbl_3"
                                        [] self \in ps -> "fork_4"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(self)] = "fork_0"
               /\ messages' = (messages \union {[To |-> q, From |-> self, Type |-> "prepare"]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ ps' = ps

proc_1(self) == Lbl_1(self)

fork_0(self) == /\ pc[self] = "fork_0"
                /\ \A q \in (participants \X participants \ { self }) : pc[q] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

P(self) == fork_0(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(self)] = "fork_2"
               /\ [To |-> self, From |-> p, Type |-> "prepare"] \in messages
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << ps, messages >>

proc_3(self) == Lbl_2(self)

fork_2(self) == /\ pc[self] = "fork_2"
                /\ \A p \in (qs \X ps) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

Q(self) == fork_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(self)] = "fork_4"
               /\ messages' = (messages \union {[To |-> q, From |-> self, Type |-> "prepare"]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ ps' = ps

proc_5(self) == Lbl_3(self)

fork_4(self) == /\ pc[self] = "fork_4"
                /\ \A q \in (ps \X qs) : pc[q] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

P1(self) == fork_4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (participants \X participants \ { self }): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (qs \X ps): proc_3(self))
           \/ (\E self \in qs: Q(self))
           \/ (\E self \in (ps \X qs): proc_5(self))
           \/ (\E self \in ps: P1(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
