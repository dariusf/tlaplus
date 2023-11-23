--------------------- MODULE Par ----------------------
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
\* BEGIN TRANSLATION (chksum(pcal) = "e2a73678" /\ chksum(tla) = "594037b8")
VARIABLES pc, x

vars == << pc, x >>

ProcSet == (participants)

Init == (* Process P *)
        /\ x = [self \in participants |-> 0]
        /\ pc = [self \in ProcSet |-> "Lbl_1"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ IF a = 1
                     ELSE /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ x' = x

P(self) == Lbl_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
