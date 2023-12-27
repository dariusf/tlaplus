--------------------- MODULE Chor ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, c1, c2

(* --algorithm Chor {
  variables
    participants = {p1, p2};
    coordinators = {c1, c2};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (P \in participants)
      variables
        committed = {};
  {
    all (p \in participants) {
      committed := committed \union {<<p, coord>>};
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "bbdbd15b" /\ chksum(tla) = "376ba544")
VARIABLES participants, coordinators, messages, me, pc, committed

vars == << participants, coordinators, messages, me, pc, committed >>

ProcSet == (("P_par_1" \X {participants})) \cup ((participants \ { me } \X participants)) \cup (("P_par_3" \X {participants})) \cup (participants)

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ coordinators = {c1, c2}
        /\ messages = {}
        /\ me = FALSE
        (* Process P *)
        /\ committed = [self \in participants |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in ("P_par_1" \X {participants}) -> "Lbl_1"
                                        [] self \in (participants \ { me } \X participants) -> "Lbl_2"
                                        [] self \in ("P_par_3" \X {participants}) -> "Lbl_3"
                                        [] self \in participants -> "Lbl_4"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Tail(self)] = "par_0"
               /\ committed' = [committed EXCEPT ![self][ me   ] = committed[self] [ me   ] \union { << me   , coord >> }]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages, me >>

proc_2(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Tail(self)] = "fork_6"
               /\ committed' = [committed EXCEPT ![self][ p ] = committed[self] [ p ] \union { << p , coord >> }]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages, me >>

proc_7(self) == Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Tail(self)] = "par_0"
               /\ pc' = [pc EXCEPT ![self] = "fork_6"]
               /\ UNCHANGED << participants, coordinators, messages, me, 
                               committed >>

fork_6(self) == /\ pc[self] = "fork_6"
                /\ \A p \in (participants \ { me } \X participants) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << participants, coordinators, messages, me, 
                                committed >>

proc_4(self) == Lbl_3(self) \/ fork_6(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ me' = self
               /\ pc' = [pc EXCEPT ![self] = "par_0"]
               /\ UNCHANGED << participants, coordinators, messages, committed >>

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_5 \in ("P_par_1", "P_par_3" \X {participants}) : pc[v_5] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, coordinators, messages, me, 
                               committed >>

P(self) == Lbl_4(self) \/ par_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ("P_par_1" \X {participants}): proc_2(self))
           \/ (\E self \in (participants \ { me } \X participants): proc_7(self))
           \/ (\E self \in ("P_par_3" \X {participants}): proc_4(self))
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
