--------------------- MODULE Par ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS c1, p1, p2

(* --algorithm Par {
  variables
    participants = {p1, p2};
    coordinators = {c1};

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (P \in participants),
    (C \in coordinators)
      variables x = 1;
  {
    all (c \in coordinators) {
      par {
        x := x + 1;
      } and {
        x := x + 2;
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "60b83e7d" /\ chksum(tla) = "3222f2c8")
VARIABLES participants, coordinators, pc, x

vars == << participants, coordinators, pc, x >>

ProcSet == (("C_par_1" \X {coordinators})) \cup (("C_par_3" \X {coordinators})) \cup (coordinators) \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c1}
        (* Process C *)
        /\ x = [self \in coordinators |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self \in ("C_par_1" \X {coordinators}) -> "Lbl_1"
                                        [] self \in ("C_par_3" \X {coordinators}) -> "Lbl_2"
                                        [] self \in coordinators -> "par_0"
                                        [] self \in participants -> "Lbl_3"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "par_0"
               /\ x' = [x EXCEPT ![self] = x[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators >>

proc_2(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(Tail(self))] = "par_0"
               /\ x' = [x EXCEPT ![self] = x[self] + 2]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators >>

proc_4(self) == Lbl_2(self)

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_5 \in ({"C_par_1", "C_par_3"} \X {coordinators}) : pc[v_5] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, x >>

C(self) == par_0(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, x >>

P(self) == Lbl_3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ("C_par_1" \X {coordinators}): proc_2(self))
           \/ (\E self \in ("C_par_3" \X {coordinators}): proc_4(self))
           \/ (\E self \in coordinators: C(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
