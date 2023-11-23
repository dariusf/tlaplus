--------------------- MODULE Cancel ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm Cancel {

  choreography
    (P \in participants)
      variables x = 0;
  {
    task P, "a" {
      par {
        cancel "a";
      } and {
        x := x + 2;
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "ccf2a011" /\ chksum(tla) = "e8bcd617")
VARIABLES cancelled_a, pc, x

vars == << cancelled_a, pc, x >>

ProcSet == ((participants \X {"P_par_1"})) \cup ((participants \X {"P_par_3"})) \cup (participants)

Init == (* Global variables *)
        /\ cancelled_a = FALSE
        (* Process P *)
        /\ x = [self \in participants |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X {"P_par_1"}) -> "Lbl_1"
                                        [] self \in (participants \X {"P_par_3"}) -> "Lbl_2"
                                        [] self \in participants -> "Lbl_3"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(self)] = "par_0"
               /\ cancelled_a' = TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ x' = x

proc_2(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(self)] = "par_0"
               /\ x' = [x EXCEPT ![self] = x[self] + 2]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED cancelled_a

proc_4(self) == Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ IF ~ cancelled_a
                     THEN /\ pc' = [pc EXCEPT ![self] = "par_0"]
                     ELSE /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << cancelled_a, x >>

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_5 \in (participants \X {"P_par_1", "P_par_3"}) : pc[v_5] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << cancelled_a, x >>

P(self) == Lbl_3(self) \/ par_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (participants \X {"P_par_1"}): proc_2(self))
           \/ (\E self \in (participants \X {"P_par_3"}): proc_4(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
