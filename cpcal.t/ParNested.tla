--------------------- MODULE Par ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm Par {
  \* variables x = 1;

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (P \in participants),
    (C = coord)
      variables x = 1;
  {
    par {
      par {
        x := x + 1;
      } and {
        x := x + 3;
      }
    } and {
      x := x + 2;
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "20b01081" /\ chksum(tla) = "927b8893")
VARIABLES pc, x

vars == << pc, x >>

ProcSet == (participants) \cup (("C_par_3" \X {coord})) \cup (("C_par_5" \X {coord})) \cup (("C_par_1" \X {coord})) \cup (("C_par_9" \X {coord})) \cup {coord}

Init == (* Process C *)
        /\ x = 1
        /\ pc = [self \in ProcSet |-> CASE self \in participants -> "Lbl_1"
                                        [] self \in ("C_par_3" \X {coord}) -> "Lbl_2"
                                        [] self \in ("C_par_5" \X {coord}) -> "Lbl_3"
                                        [] self \in ("C_par_1" \X {coord}) -> "Lbl_4"
                                        [] self \in ("C_par_9" \X {coord}) -> "Lbl_5"
                                        [] self = coord -> "par_0"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ x' = x

P(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Tail(self)] = "par_2"
               /\ x' = x + 1
               /\ pc' = [pc EXCEPT ![self] = "Done"]

proc_4(self) == Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Tail(self)] = "par_2"
               /\ x' = x + 3
               /\ pc' = [pc EXCEPT ![self] = "Done"]

proc_6(self) == Lbl_3(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Tail(self)] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "par_2"]
               /\ x' = x

par_2(self) == /\ pc[self] = "par_2"
               /\ \A v_7 \in ({"C_par_3", "C_par_5"} \X {coord}) : pc[v_7] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ x' = x

proc_8(self) == Lbl_4(self) \/ par_2(self)

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ pc[Tail(self)] = "par_0"
               /\ x' = x + 2
               /\ pc' = [pc EXCEPT ![self] = "Done"]

proc_10(self) == Lbl_5(self)

par_0 == /\ pc[coord] = "par_0"
         /\ \A v_11 \in ({"C_par_1", "C_par_9"} \X {coord}) : pc[v_11] = "Done"
         /\ pc' = [pc EXCEPT ![coord] = "Done"]
         /\ x' = x

C == par_0

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in participants: P(self))
           \/ (\E self \in ("C_par_3" \X {coord}): proc_4(self))
           \/ (\E self \in ("C_par_5" \X {coord}): proc_6(self))
           \/ (\E self \in ("C_par_1" \X {coord}): proc_8(self))
           \/ (\E self \in ("C_par_9" \X {coord}): proc_10(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
