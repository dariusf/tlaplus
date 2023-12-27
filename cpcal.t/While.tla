--------------------- MODULE While ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm While {
  variables
    participants = {p1, p2};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (C = coord)
      variables y = 3,
    (P \in participants)
      variables x = 1;
  {
    all (p \in participants) {
      while (y > 1), (x < 3) {
        Transmit(coord, p, 5);
        y := y - 1;
        x := x + 1;
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "84c6a88a" /\ chksum(tla) = "cb212a2b")
VARIABLES participants, messages, pc, y, x

vars == << participants, messages, pc, y, x >>

ProcSet == ((participants \X coord)) \cup {coord} \cup (("P_par_3" \X {participants})) \cup ((participants \ { Tail(self) } \X participants)) \cup (("P_par_5" \X {participants})) \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ messages = {}
        (* Process C *)
        /\ y = 3
        (* Process P *)
        /\ x = [self \in participants |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self \in (participants \X coord) -> "Lbl_1"
                                        [] self = coord -> "fork_0"
                                        [] self \in ("P_par_3" \X {participants}) -> "Lbl_3"
                                        [] self \in (participants \ { Tail(self) } \X participants) -> "Lbl_5"
                                        [] self \in ("P_par_5" \X {participants}) -> "Lbl_7"
                                        [] self \in participants -> "par_2"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Tail(self)] = "fork_0"
               /\ pc' = [pc EXCEPT ![self] = "Lbl_2"]
               /\ UNCHANGED << participants, messages, y, x >>

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ IF y > 1
                     THEN /\ TRUE
                          /\ y' = y - 1
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ y' = y
               /\ UNCHANGED << participants, messages, x >>

proc_1(self) == Lbl_1(self) \/ Lbl_2(self)

fork_0 == /\ pc[coord] = "fork_0"
          /\ \A p \in (participants \X coord) : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![coord] = "Done"]
          /\ UNCHANGED << participants, messages, y, x >>

C == fork_0

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Tail(self)] = "par_2"
               /\ pc' = [pc EXCEPT ![self] = "Lbl_4"]
               /\ UNCHANGED << participants, messages, y, x >>

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ IF x[self] [ Tail(self)] < 3
                     THEN /\ [To |-> Tail(self), From |-> coord, Type |-> 5] \in messages
                          /\ TRUE
                          /\ x' = [x EXCEPT ![self][ Tail(self)] = x[self] [ Tail(self)] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_4"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ x' = x
               /\ UNCHANGED << participants, messages, y >>

proc_4(self) == Lbl_3(self) \/ Lbl_4(self)

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ pc[Tail(self)] = "fork_8"
               /\ pc' = [pc EXCEPT ![self] = "Lbl_6"]
               /\ UNCHANGED << participants, messages, y, x >>

Lbl_6(self) == /\ pc[self] = "Lbl_6"
               /\ IF x[self] [ Head(self)] < 3
                     THEN /\ TRUE
                          /\ TRUE
                          /\ x' = [x EXCEPT ![self][ Head(self)] = x[self] [ Head(self)] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_6"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ x' = x
               /\ UNCHANGED << participants, messages, y >>

proc_9(self) == Lbl_5(self) \/ Lbl_6(self)

Lbl_7(self) == /\ pc[self] = "Lbl_7"
               /\ pc[Tail(self)] = "par_2"
               /\ pc' = [pc EXCEPT ![self] = "fork_8"]
               /\ UNCHANGED << participants, messages, y, x >>

fork_8(self) == /\ pc[self] = "fork_8"
                /\ \A p \in (participants \ { Tail(self) } \X participants) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, messages, y, x >>

proc_6(self) == Lbl_7(self) \/ fork_8(self)

par_2(self) == /\ pc[self] = "par_2"
               /\ \A v_7 \in ({"P_par_3", "P_par_5"} \X {participants}) : pc[v_7] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, messages, y, x >>

P(self) == par_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in (participants \X coord): proc_1(self))
           \/ (\E self \in ("P_par_3" \X {participants}): proc_4(self))
           \/ (\E self \in (participants \ { Tail(self) } \X participants): proc_9(self))
           \/ (\E self \in ("P_par_5" \X {participants}): proc_6(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
