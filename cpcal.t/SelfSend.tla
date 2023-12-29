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
\* BEGIN TRANSLATION (chksum(pcal) = "436c185e" /\ chksum(tla) = "414a1967")
VARIABLES ps, messages, pc

vars == << ps, messages, pc >>

ProcSet == ((participants \ { Head(Tail(self)) } \X participants)) \cup (participants) \cup ((qs \X ps)) \cup (ps) \cup ((ps \X qs)) \cup (qs)

Init == (* Global variables *)
        /\ ps = {p1, p2}
        /\ messages = {}
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \ { Head(Tail(self)) } \X participants) -> "Lbl_1"
                                        [] self \in participants -> "fork_0"
                                        [] self \in (qs \X ps) -> "Lbl_2"
                                        [] self \in ps -> "fork_3"
                                        [] self \in (ps \X qs) -> "Lbl_3"
                                        [] self \in qs -> "fork_6"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "fork_0"
               /\ pc' = [pc EXCEPT ![self] = "comm_2"]
               /\ UNCHANGED << ps, messages >>

comm_2(self) == /\ pc[self] = "comm_2"
                /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "prepare"]})
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ ps' = ps

proc_1(self) == Lbl_1(self) \/ comm_2(self)

fork_0(self) == /\ pc[self] = "fork_0"
                /\ \A q \in (participants \ { Head(Tail(self)) } \X participants) : pc[q] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

P(self) == fork_0(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(Tail(self))] = "fork_3"
               /\ pc' = [pc EXCEPT ![self] = "comm_5"]
               /\ UNCHANGED << ps, messages >>

comm_5(self) == /\ pc[self] = "comm_5"
                /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> "prepare"]})
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ ps' = ps

proc_4(self) == Lbl_2(self) \/ comm_5(self)

fork_3(self) == /\ pc[self] = "fork_3"
                /\ \A q \in (qs \X ps) : pc[q] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

P1(self) == fork_3(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(Tail(self))] = "fork_6"
               /\ pc' = [pc EXCEPT ![self] = "comm_8"]
               /\ UNCHANGED << ps, messages >>

comm_8(self) == /\ pc[self] = "comm_8"
                /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "prepare"] \in messages
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

proc_7(self) == Lbl_3(self) \/ comm_8(self)

fork_6(self) == /\ pc[self] = "fork_6"
                /\ \A p \in (ps \X qs) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ps, messages >>

Q(self) == fork_6(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (participants \ { Head(Tail(self)) } \X participants): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (qs \X ps): proc_4(self))
           \/ (\E self \in ps: P1(self))
           \/ (\E self \in (ps \X qs): proc_7(self))
           \/ (\E self \in qs: Q(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
