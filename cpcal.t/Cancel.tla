--------------------- MODULE Cancel ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, c1

(* --algorithm Cancel {
  variables
    participants = {p1, p2};
    coordinators = {c1};

  choreography
    (C \in coordinators),
    (P \in participants)
      variables x = 0;
  {
    all (c \in coordinators) {
      all (p \in participants) {
        task P, "a" {
          par {
            cancel "a";
          } and {
            x := x + 2;
          }
        }
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "910b4638" /\ chksum(tla) = "7afc15d2")
VARIABLES participants, coordinators, cancelled_a, pc, x

vars == << participants, coordinators, cancelled_a, pc, x >>

ProcSet == (coordinators) \cup ((coordinators \X participants)) \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c1}
        /\ cancelled_a = FALSE
        (* Process P *)
        /\ x = [self \in participants |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in coordinators -> "Lbl_1"
                                        [] self \in (coordinators \X participants) -> "Lbl_2"
                                        [] self \in participants -> "fork_0"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, cancelled_a, x >>

C(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(Tail(self))] = "fork_0"
               /\ IF ~ cancelled_a
                     THEN /\ x' = [x EXCEPT ![self] = x[self] + 2]
                     ELSE /\ TRUE
                          /\ x' = x
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, cancelled_a >>

proc_1(self) == Lbl_2(self)

fork_0(self) == /\ pc[self] = "fork_0"
                /\ \A c \in (coordinators \X participants) : pc[c] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, cancelled_a, x >>

P(self) == fork_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in coordinators: C(self))
           \/ (\E self \in (coordinators \X participants): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
