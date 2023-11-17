--------------------- MODULE Chor ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm Chor {
  variables
    participants = {p1, p2};
    out = {};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (P \in participants),
    (C = coord)
      variables
        aborted = {},
        committed = {},
        has_aborted = FALSE;
  {
    all (p \in participants) {
      Send(coord, p, "prepare");
      out := out \union {<<p, coord>>};
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "63de594" /\ chksum(tla) = "7ce7a561")
VARIABLES participants, out, messages, pc, aborted, committed, has_aborted

vars == << participants, out, messages, pc, aborted, committed, has_aborted
        >>

ProcSet == ((participants \X participants)) \cup (participants) \cup ((coord \X participants)) \cup {coord}

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ out = {}
        /\ messages = {}
        (* Process C *)
        /\ aborted = {}
        /\ committed = {}
        /\ has_aborted = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X participants) -> "Lbl_1"
                                        [] self \in participants -> "fork_0"
                                        [] self \in (coord \X participants) -> "Lbl_2"
                                        [] self = coord -> "fork_2"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(self)] = "fork_0"
               /\ [To |-> self, From |-> coord, Type |-> "prepare"] \in messages
               /\ out' = (out \union {<<p, coord>>})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, messages, aborted, committed, 
                               has_aborted >>

proc_1(self) == Lbl_1(self)

fork_0(self) == /\ pc[self] = "fork_0"
                /\ \A p \in (participants \X participants) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, out, messages, aborted, 
                                committed, has_aborted >>

P(self) == fork_0(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(self)] = "fork_2"
               /\ messages' = (messages \union {[To |-> self, From |-> p, Type |-> "prepare"]})
               /\ out' = (out \union {<<p, coord>>})
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, aborted, committed, has_aborted >>

proc_3(self) == Lbl_2(self)

fork_2 == /\ pc[coord] = "fork_2"
          /\ \A p \in (coord \X participants) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![coord] = "Done"]
          /\ UNCHANGED << participants, out, messages, aborted, committed, 
                          has_aborted >>

C == fork_2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in (participants \X participants): proc_1(self))
           \/ (\E self \in participants: P(self))
           \/ (\E self \in (coord \X participants): proc_3(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
