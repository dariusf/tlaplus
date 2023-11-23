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
\* BEGIN TRANSLATION (chksum(pcal) = "7b420d41" /\ chksum(tla) = "7c72e6b6")
VARIABLES participants, coordinators, messages, cancelled_phase1, pc

vars == << participants, coordinators, messages, cancelled_phase1, pc >>

ProcSet == (participants) \cup ((c \X participants)) \cup ((c \X participants)) \cup ((c \X participants)) \cup {c}

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c}
        /\ messages = {}
        /\ cancelled_phase1 = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in participants -> "Lbl_1"
                                        [] self \in (c \X participants) -> "Lbl_4"
                                        [] self \in (c \X participants) -> "Lbl_5"
                                        [] self \in (c \X participants) -> "Lbl_6"
                                        [] self = c -> "Lbl_7"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ [To |-> self, From |-> c, Type |-> "prepare"] \in messages
               /\ \/ /\ messages' = (messages \union {[To |-> self, From |-> c, Type |-> "prepared"]})
                  \/ /\ messages' = (messages \union {[To |-> self, From |-> c, Type |-> "aborted"]})
                     /\ TRUE
               /\ IF aborted
                     THEN /\ [To |-> self, From |-> c, Type |-> "abort"] \in messages'
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_2"]
                     ELSE /\ [To |-> self, From |-> c, Type |-> "commit"] \in messages'
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_3"]
               /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ messages' = (messages \union {[To |-> self, From |-> c, Type |-> "aborted"]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ messages' = (messages \union {[To |-> self, From |-> c, Type |-> "committed"]})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

P(self) == Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Head(self)] = "fork_0"
               /\ messages' = (messages \union {[To |-> self, From |-> p, Type |-> "prepare"]})
               /\ \/ /\ [To |-> self, From |-> p, Type |-> "prepared"] \in messages'
                     /\ UNCHANGED cancelled_phase1
                  \/ /\ [To |-> self, From |-> p, Type |-> "aborted"] \in messages'
                     /\ cancelled_phase1' = TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators >>

proc_1(self) == Lbl_4(self)

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ pc[Head(self)] = "fork_2"
               /\ messages' = (messages \union {[To |-> self, From |-> p, Type |-> "abort"]})
               /\ [To |-> self, From |-> p, Type |-> "aborted"] \in messages'
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

proc_3(self) == Lbl_5(self)

Lbl_6(self) == /\ pc[self] = "Lbl_6"
               /\ pc[Head(self)] = "fork_4"
               /\ messages' = (messages \union {[To |-> self, From |-> p, Type |-> "commit"]})
               /\ [To |-> self, From |-> p, Type |-> "committed"] \in messages'
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

proc_5(self) == Lbl_6(self)

Lbl_7 == /\ pc[c] = "Lbl_7"
         /\ IF ~ cancelled_phase1
               THEN /\ pc' = [pc EXCEPT ![c] = "fork_0"]
               ELSE /\ TRUE
                    /\ pc' = [pc EXCEPT ![c] = "Lbl_8"]
         /\ UNCHANGED << participants, coordinators, messages, 
                         cancelled_phase1 >>

fork_0 == /\ pc[c] = "fork_0"
          /\ \A p \in (c \X participants) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![c] = "Lbl_8"]
          /\ UNCHANGED << participants, coordinators, messages, 
                          cancelled_phase1 >>

Lbl_8 == /\ pc[c] = "Lbl_8"
         /\ IF aborted
               THEN /\ pc' = [pc EXCEPT ![c] = "fork_2"]
               ELSE /\ pc' = [pc EXCEPT ![c] = "fork_4"]
         /\ UNCHANGED << participants, coordinators, messages, 
                         cancelled_phase1 >>

fork_2 == /\ pc[c] = "fork_2"
          /\ \A p \in (c \X participants) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![c] = "Done"]
          /\ UNCHANGED << participants, coordinators, messages, 
                          cancelled_phase1 >>

fork_4 == /\ pc[c] = "fork_4"
          /\ \A p \in (c \X participants) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![c] = "Done"]
          /\ UNCHANGED << participants, coordinators, messages, 
                          cancelled_phase1 >>

C == Lbl_7 \/ fork_0 \/ Lbl_8 \/ fork_2 \/ fork_4

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (c \X participants): proc_1(self))
           \/ (\E self \in (c \X participants): proc_3(self))
           \/ (\E self \in (c \X participants): proc_5(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
