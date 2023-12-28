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
\* BEGIN TRANSLATION (chksum(pcal) = "2a9e826" /\ chksum(tla) = "cbfde33f")
VARIABLES participants, coordinators, messages, cancelled_phase1, pc

vars == << participants, coordinators, messages, cancelled_phase1, pc >>

ProcSet == ((participants \X c)) \cup {c} \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c}
        /\ messages = {}
        /\ cancelled_phase1 = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X c) -> "Lbl_1"
                                        [] self = c -> "Lbl_2"
                                        [] self \in participants -> "comm_2"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "fork_0"
               /\ cancelled_phase1' = TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages >>

proc_1(self) == Lbl_1(self)

Lbl_2 == /\ pc[c] = "Lbl_2"
         /\ IF ~ cancelled_phase1
               THEN /\ pc' = [pc EXCEPT ![c] = "fork_0"]
               ELSE /\ TRUE
                    /\ pc' = [pc EXCEPT ![c] = "Lbl_3"]
         /\ UNCHANGED << participants, coordinators, messages, 
                         cancelled_phase1 >>

fork_0 == /\ pc[c] = "fork_0"
          /\ \A p \in (participants \X c) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![c] = "Lbl_3"]
          /\ UNCHANGED << participants, coordinators, messages, 
                          cancelled_phase1 >>

Lbl_3 == /\ pc[c] = "Lbl_3"
         /\ IF aborted
               THEN /\ TRUE
               ELSE /\ TRUE
         /\ pc' = [pc EXCEPT ![c] = "Done"]
         /\ UNCHANGED << participants, coordinators, messages, 
                         cancelled_phase1 >>

C == Lbl_2 \/ fork_0 \/ Lbl_3

comm_2(self) == /\ pc[self] = "comm_2"
                /\ [To |-> Head(Tail(self)), From |-> c, Type |-> "prepare"] \in messages
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "comm_3"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "comm_4"]
                /\ UNCHANGED << participants, coordinators, messages, 
                                cancelled_phase1 >>

comm_3(self) == /\ pc[self] = "comm_3"
                /\ messages' = (messages \union {[To |-> c, From |-> Head(Tail(self)), Type |-> "prepared"]})
                /\ pc' = [pc EXCEPT ![self] = "Lbl_4"]
                /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

comm_4(self) == /\ pc[self] = "comm_4"
                /\ messages' = (messages \union {[To |-> c, From |-> Head(Tail(self)), Type |-> "aborted"]})
                /\ pc' = [pc EXCEPT ![self] = "Lbl_4"]
                /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ IF aborted
                     THEN /\ pc' = [pc EXCEPT ![self] = "comm_5"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "comm_7"]
               /\ UNCHANGED << participants, coordinators, messages, 
                               cancelled_phase1 >>

comm_5(self) == /\ pc[self] = "comm_5"
                /\ [To |-> Head(Tail(self)), From |-> c, Type |-> "abort"] \in messages
                /\ pc' = [pc EXCEPT ![self] = "comm_6"]
                /\ UNCHANGED << participants, coordinators, messages, 
                                cancelled_phase1 >>

comm_6(self) == /\ pc[self] = "comm_6"
                /\ messages' = (messages \union {[To |-> c, From |-> Head(Tail(self)), Type |-> "aborted"]})
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

comm_7(self) == /\ pc[self] = "comm_7"
                /\ [To |-> Head(Tail(self)), From |-> c, Type |-> "commit"] \in messages
                /\ pc' = [pc EXCEPT ![self] = "comm_8"]
                /\ UNCHANGED << participants, coordinators, messages, 
                                cancelled_phase1 >>

comm_8(self) == /\ pc[self] = "comm_8"
                /\ messages' = (messages \union {[To |-> c, From |-> Head(Tail(self)), Type |-> "committed"]})
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, cancelled_phase1 >>

P(self) == comm_2(self) \/ comm_3(self) \/ comm_4(self) \/ Lbl_4(self)
              \/ comm_5(self) \/ comm_6(self) \/ comm_7(self)
              \/ comm_8(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in (participants \X c): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
