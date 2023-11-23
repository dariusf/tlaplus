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
      x := x + 1;
    } and {
      x := x + 2;
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "97bb10fc" /\ chksum(tla) = "43b0bd7d")
VARIABLES pc, x

vars == << pc, x >>

ProcSet == ((coord \X {"C_par_1"})) \cup ((coord \X {"C_par_3"})) \cup {coord} \cup ((participants \X {"P_par_7"})) \cup ((participants \X {"P_par_9"})) \cup (participants)

Init == (* Process C *)
        /\ x = 1
        /\ pc = [self \in ProcSet |-> CASE self \in (coord \X {"C_par_1"}) -> "Lbl_1"
                                        [] self \in (coord \X {"C_par_3"}) -> "Lbl_2"
                                        [] self = coord -> "par_0"
                                        [] self \in (participants \X {"P_par_7"}) -> "Lbl_3"
                                        [] self \in (participants \X {"P_par_9"}) -> "Lbl_4"
                                        [] self \in participants -> "par_6"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(self)] = "par_0"
               /\ x' = x + 1
               /\ pc' = [pc EXCEPT ![self] = "Done"]

proc_2(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(self)] = "par_0"
               /\ x' = x + 2
               /\ pc' = [pc EXCEPT ![self] = "Done"]

proc_4(self) == Lbl_2(self)

par_0 == /\ pc[coord] = "par_0"
         /\ \A v_5 \in (coord \X {"C_par_1", "C_par_3"}) : pc[v_5] = "Done"
         /\ pc' = [pc EXCEPT ![coord] = "Done"]
         /\ x' = x

C == par_0

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(self)] = "par_6"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ x' = x

proc_8(self) == Lbl_3(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Head(self)] = "par_6"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ x' = x

proc_10(self) == Lbl_4(self)

par_6(self) == /\ pc[self] = "par_6"
               /\ \A v_11 \in (participants \X {"P_par_7", "P_par_9"}) : pc[v_11] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ x' = x

P(self) == par_6(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in (coord \X {"C_par_1"}): proc_2(self))
           \/ (\E self \in (coord \X {"C_par_3"}): proc_4(self))
           \/ (\E self \in (participants \X {"P_par_7"}): proc_8(self))
           \/ (\E self \in (participants \X {"P_par_9"}): proc_10(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
