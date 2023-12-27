--------------------- MODULE TwoPhaseCommit ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, c

(* --algorithm TwoPhaseCommit {
  variables
    participants = {p1, p2};
    coordinators = {c};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (C = c);
    (P \in participants);
  {
    task C, "phase1" {
      all (p \in participants) {
        Transmit(c, p, "prepare");
        either {
          Transmit(p, c, "prepared");
        } or {
          Transmit(p, c, "aborted");
          cancel "phase1";
        }
      }
    };
    if (aborted) {
      all (p \in participants) {
        Transmit(c, p, "abort");
        Transmit(p, c, "aborted");
      }
    } else {
      all (p \in participants) {
        Transmit(c, p, "commit");
        Transmit(p, c, "committed");
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "653d9480" /\ chksum(tla) = "91985464")
VARIABLES participants, coordinators, messages, cancelled_phase1, pc

vars == << participants, coordinators, messages, cancelled_phase1, pc >>

ProcSet == (participants) \cup ((participants \X c)) \cup {c}

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c}
        /\ messages = {}
        /\ cancelled_phase1 = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in participants -> "Lbl_1"
                                        [] self \in (participants \X c) -> "Lbl_4"
                                        [] self = c -> "Lbl_5"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ [To |-> Tail(self), From |-> c, Type |-> prepare] \in messages
               /\ \/ /\ messages' = (messages \union {[To |-> c, From |-> Tail(self), Type |-> prepared]})
                  \/ /\ messages' = (messages \union {[To |-> c, From |-> Tail(self), Type |-> aborted]})
               /\ IF aborted
                     THEN /\ [To |-> Tail(self), From |-> c, Type |-> abort] \in messages'
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_2"]
                     ELSE /\ [To |-> Tail(self), From |-> c, Type |-> commit] \in messages'
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_3"]
               /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ messages' = (messages \union {[To |-> c, From |-> Tail(self), Type |-> aborted]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ messages' = (messages \union {[To |-> c, From |-> Tail(self), Type |-> committed]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

P(self) == Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Tail(self)] = "fork_0"
               /\ cancelled_phase1' = TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages >>

proc_1(self) == Lbl_4(self)

Lbl_5 == /\ pc[c] = "Lbl_5"
         /\ IF ~ cancelled_phase1
               THEN /\ pc' = [pc EXCEPT ![c] = "fork_0"]
               ELSE /\ TRUE
                    /\ pc' = [pc EXCEPT ![c] = "Lbl_6"]
         /\ UNCHANGED << participants, coordinators, messages, 
                         cancelled_phase1 >>

fork_0 == /\ pc[c] = "fork_0"
          /\ \A p \in (participants \X c) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![c] = "Lbl_6"]
          /\ UNCHANGED << participants, coordinators, messages, 
                          cancelled_phase1 >>

Lbl_6 == /\ pc[c] = "Lbl_6"
         /\ IF aborted
               THEN /\ TRUE
               ELSE /\ TRUE
         /\ pc' = [pc EXCEPT ![c] = "Done"]
         /\ UNCHANGED << participants, coordinators, messages, 
                         cancelled_phase1 >>

C == Lbl_5 \/ fork_0 \/ Lbl_6

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (participants \X c): proc_1(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
