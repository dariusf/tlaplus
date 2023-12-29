--------------------- MODULE Paxos ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, a1, a2, l1

(* --algorithm Paxos {
  variables
    proposers = {p1, p2};
    acceptors = {p1, p2};
    learners = {l1};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (L \in learners),
    (P \in proposers)
      variables
        proposal = 0,
        value = 1,
        cp = <<0, 0>>,
        majority = size(acceptors) / 2 + 1,
        promise_responses = {};
    (A \in acceptors)
      variables
        highest_proposal = <<0, 0>>,
        accepted_proposal = <<0, 0>>,
        accepted_value = 0;
  {
    all (p \in proposers) {
      par {
        proposal := proposal + 1;
        all (a \in acceptors) {
          Transmit(p, a, <<"prepare", <<p, proposal>>>>);
          \* n
          if (n > highest_proposal) {
            highest_proposal := n;
            Transmit(a, p, <<"promise", [cp |-> accepted_proposal, cv |-> accepted_value]>>);
            \* resp
            promise_responses := promise_responses \union {a};
            if (resp.cp > <<0, 0>> /\ resp.cp > cp) {
              cp := resp.cp;
              value := resp.cv;
            }
          }
        }
      } and {
        await Size(promise_responses) > majority;
        all (a1 \in promise_responses) {
          Transmit(p, a1, <<"propose", [pn |-> proposal, pv |-> value, a1 |-> a1]>>);
          \* msg
          if (msg.pn = highest_proposal) {
            accepted_proposal[a1] := pn;
            accepted_value[a1] := pv;
            Transmit(a1, p, "accept");
            all (l \in learners) {
              Transmit(a1, l, "accept");
            }
          }
        }
      }
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "4df4f3bc" /\ chksum(tla) = "8e03194a")
VARIABLES proposers, acceptors, learners, messages, pc, proposal, value, cp, 
          majority, promise_responses, highest_proposal, accepted_proposal, 
          accepted_value

vars == << proposers, acceptors, learners, messages, pc, proposal, value, cp, 
           majority, promise_responses, highest_proposal, accepted_proposal, 
           accepted_value >>

ProcSet == ((promise_responses \X learners)) \cup ((proposers \X learners)) \cup (learners) \cup ((acceptors \X proposers)) \cup (("P_par_8" \X {proposers})) \cup ((promise_responses \X proposers)) \cup (("P_par_10" \X {proposers})) \cup (("P_par_6" \X {proposers})) \cup ((proposers \ { Head(Tail(self)) } \X proposers)) \cup (("P_par_14" \X {proposers})) \cup (proposers) \cup (("A_par_28" \X {acceptors})) \cup (("A_par_30" \X {acceptors})) \cup ((proposers \X acceptors)) \cup (acceptors)

Init == (* Global variables *)
        /\ proposers = {p1, p2}
        /\ acceptors = {p1, p2}
        /\ learners = {l1}
        /\ messages = {}
        (* Process P *)
        /\ proposal = [self \in proposers |-> 0]
        /\ value = [self \in proposers |-> 1]
        /\ cp = [self \in proposers |-> <<0, 0>>]
        /\ majority = [self \in proposers |-> size(acceptors) / 2 + 1]
        /\ promise_responses = [self \in proposers |-> {}]
        (* Process A *)
        /\ highest_proposal = [self \in acceptors |-> <<0, 0>>]
        /\ accepted_proposal = [self \in acceptors |-> <<0, 0>>]
        /\ accepted_value = [self \in acceptors |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in (promise_responses \X learners) -> "Lbl_1"
                                        [] self \in (proposers \X learners) -> "Lbl_2"
                                        [] self \in learners -> "fork_0"
                                        [] self \in (acceptors \X proposers) -> "Lbl_3"
                                        [] self \in ("P_par_8" \X {proposers}) -> "Lbl_4"
                                        [] self \in (promise_responses \X proposers) -> "Lbl_5"
                                        [] self \in ("P_par_10" \X {proposers}) -> "Lbl_6"
                                        [] self \in ("P_par_6" \X {proposers}) -> "Lbl_7"
                                        [] self \in (proposers \ { Head(Tail(self)) } \X proposers) -> "Lbl_8"
                                        [] self \in ("P_par_14" \X {proposers}) -> "Lbl_9"
                                        [] self \in proposers -> "par_5"
                                        [] self \in ("A_par_28" \X {acceptors}) -> "Lbl_10"
                                        [] self \in ("A_par_30" \X {acceptors}) -> "Lbl_11"
                                        [] self \in (proposers \X acceptors) -> "Lbl_12"
                                        [] self \in acceptors -> "fork_35"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "fork_1"
               /\ IF msg.pn = highest_proposal[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "comm_4"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

comm_4(self) == /\ pc[self] = "comm_4"
                /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "accept"] \in messages
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                proposal, value, cp, majority, 
                                promise_responses, highest_proposal, 
                                accepted_proposal, accepted_value >>

proc_2(self) == Lbl_1(self) \/ comm_4(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ pc[Head(Tail(self))] = "fork_0"
               /\ Size ( promise_responses[self] ) > majority[self]
               /\ pc' = [pc EXCEPT ![self] = "fork_1"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

fork_1(self) == /\ pc[self] = "fork_1"
                /\ \A a1 \in ( promise_responses[self] \X learners ) : pc [ a1 ] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                proposal, value, cp, majority, 
                                promise_responses, highest_proposal, 
                                accepted_proposal, accepted_value >>

proc_3(self) == Lbl_2(self) \/ fork_1(self)

fork_0(self) == /\ pc[self] = "fork_0"
                /\ \A p \in (proposers \X learners) : pc[p] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                proposal, value, cp, majority, 
                                promise_responses, highest_proposal, 
                                accepted_proposal, accepted_value >>

L(self) == fork_0(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(Tail(self))] = "fork_17"
               /\ pc' = [pc EXCEPT ![self] = "comm_19"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

comm_19(self) == /\ pc[self] = "comm_19"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> (<< "prepare" , << Head(Tail(self)) , proposal[self] >> >>)]})
                 /\ IF n > highest_proposal[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "comm_20"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, proposal, 
                                 value, cp, majority, promise_responses, 
                                 highest_proposal, accepted_proposal, 
                                 accepted_value >>

comm_20(self) == /\ pc[self] = "comm_20"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> (<< "promise" , [ cp |-> accepted_proposal[self] , cv |-> accepted_value[self] ] >>)] \in messages
                 /\ promise_responses' = [promise_responses EXCEPT ![self] = promise_responses[self] \union { Head(self)}]
                 /\ IF resp.cp > <<0, 0>> /\ resp.cp > cp[self]
                       THEN /\ cp' = [cp EXCEPT ![self] = resp . cp]
                            /\ value' = [value EXCEPT ![self] = resp . cv]
                       ELSE /\ TRUE
                            /\ UNCHANGED << value, cp >>
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                 proposal, majority, highest_proposal, 
                                 accepted_proposal, accepted_value >>

proc_18(self) == Lbl_3(self) \/ comm_19(self) \/ comm_20(self)

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ pc[Head(Tail(self))] = "par_7"
               /\ proposal' = [proposal EXCEPT ![self] = proposal[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "fork_17"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, value, 
                               cp, majority, promise_responses, 
                               highest_proposal, accepted_proposal, 
                               accepted_value >>

fork_17(self) == /\ pc[self] = "fork_17"
                 /\ \A a \in (acceptors \X proposers) : pc[a] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                 proposal, value, cp, majority, 
                                 promise_responses, highest_proposal, 
                                 accepted_proposal, accepted_value >>

proc_9(self) == Lbl_4(self) \/ fork_17(self)

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ pc[Head(Tail(self))] = "fork_21"
               /\ pc' = [pc EXCEPT ![self] = "comm_23"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

comm_23(self) == /\ pc[self] = "comm_23"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> (<< "propose" , [ pn |-> proposal[self] , pv |-> value[self] , Head(self)|-> Head(self)] >>)]})
                 /\ IF msg.pn = highest_proposal[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "comm_24"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, proposal, 
                                 value, cp, majority, promise_responses, 
                                 highest_proposal, accepted_proposal, 
                                 accepted_value >>

comm_24(self) == /\ pc[self] = "comm_24"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> "accept"] \in messages
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                 proposal, value, cp, majority, 
                                 promise_responses, highest_proposal, 
                                 accepted_proposal, accepted_value >>

proc_22(self) == Lbl_5(self) \/ comm_23(self) \/ comm_24(self)

Lbl_6(self) == /\ pc[self] = "Lbl_6"
               /\ pc[Head(Tail(self))] = "par_7"
               /\ Size ( promise_responses[self] ) > majority[self]
               /\ pc' = [pc EXCEPT ![self] = "fork_21"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

fork_21(self) == /\ pc[self] = "fork_21"
                 /\ \A a1 \in (promise_responses[self] \X proposers) : pc[a1] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                 proposal, value, cp, majority, 
                                 promise_responses, highest_proposal, 
                                 accepted_proposal, accepted_value >>

proc_11(self) == Lbl_6(self) \/ fork_21(self)

Lbl_7(self) == /\ pc[self] = "Lbl_7"
               /\ pc[Head(Tail(self))] = "par_5"
               /\ pc' = [pc EXCEPT ![self] = "par_7"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

par_7(self) == /\ pc[self] = "par_7"
               /\ \A v_12 \in ({"P_par_8", "P_par_10"} \X {proposers}) : pc[v_12] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

proc_13(self) == Lbl_7(self) \/ par_7(self)

Lbl_8(self) == /\ pc[self] = "Lbl_8"
               /\ pc[Head(Tail(self))] = "fork_25"
               /\ Size ( promise_responses[self] ) > majority[self]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

proc_26(self) == Lbl_8(self)

Lbl_9(self) == /\ pc[self] = "Lbl_9"
               /\ pc[Head(Tail(self))] = "par_5"
               /\ pc' = [pc EXCEPT ![self] = "fork_25"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

fork_25(self) == /\ pc[self] = "fork_25"
                 /\ \A p \in (proposers \ { Head(Tail(self)) } \X proposers) : pc[p] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                 proposal, value, cp, majority, 
                                 promise_responses, highest_proposal, 
                                 accepted_proposal, accepted_value >>

proc_15(self) == Lbl_9(self) \/ fork_25(self)

par_5(self) == /\ pc[self] = "par_5"
               /\ \A v_16 \in ({"P_par_6", "P_par_14"} \X {proposers}) : pc[v_16] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << proposers, acceptors, learners, messages, 
                               proposal, value, cp, majority, 
                               promise_responses, highest_proposal, 
                               accepted_proposal, accepted_value >>

P(self) == par_5(self)

Lbl_10(self) == /\ pc[self] = "Lbl_10"
                /\ pc[Head(Tail(self))] = "par_27"
                /\ pc' = [pc EXCEPT ![self] = "comm_33"]
                /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                proposal, value, cp, majority, 
                                promise_responses, highest_proposal, 
                                accepted_proposal, accepted_value >>

comm_33(self) == /\ pc[self] = "comm_33"
                 /\ [To |-> Head(Tail(self)), From |-> p, Type |-> (<< "prepare" , << p , proposal[self] >> >>)] \in messages
                 /\ IF n > highest_proposal[self]
                       THEN /\ highest_proposal' = [highest_proposal EXCEPT ![self] = n]
                            /\ pc' = [pc EXCEPT ![self] = "comm_34"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED highest_proposal
                 /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                 proposal, value, cp, majority, 
                                 promise_responses, accepted_proposal, 
                                 accepted_value >>

comm_34(self) == /\ pc[self] = "comm_34"
                 /\ messages' = (messages \union {[To |-> p, From |-> Head(Tail(self)), Type |-> (<< "promise" , [ cp |-> accepted_proposal[self] , cv |-> accepted_value[self] ] >>)]})
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, proposal, 
                                 value, cp, majority, promise_responses, 
                                 highest_proposal, accepted_proposal, 
                                 accepted_value >>

proc_29(self) == Lbl_10(self) \/ comm_33(self) \/ comm_34(self)

Lbl_11(self) == /\ pc[self] = "Lbl_11"
                /\ pc[Head(Tail(self))] = "par_27"
                /\ Size ( promise_responses[self] ) > majority[self]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                proposal, value, cp, majority, 
                                promise_responses, highest_proposal, 
                                accepted_proposal, accepted_value >>

proc_31(self) == Lbl_11(self)

Lbl_12(self) == /\ pc[self] = "Lbl_12"
                /\ pc[Head(Tail(self))] = "fork_35"
                /\ pc' = [pc EXCEPT ![self] = "par_27"]
                /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                proposal, value, cp, majority, 
                                promise_responses, highest_proposal, 
                                accepted_proposal, accepted_value >>

par_27(self) == /\ pc[self] = "par_27"
                /\ \A v_32 \in ( { "A_par_28" , "A_par_30" } \X { acceptors } ) : pc [ v_32 ] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                proposal, value, cp, majority, 
                                promise_responses, highest_proposal, 
                                accepted_proposal, accepted_value >>

proc_36(self) == Lbl_12(self) \/ par_27(self)

fork_35(self) == /\ pc[self] = "fork_35"
                 /\ \A p \in (proposers \X acceptors) : pc[p] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << proposers, acceptors, learners, messages, 
                                 proposal, value, cp, majority, 
                                 promise_responses, highest_proposal, 
                                 accepted_proposal, accepted_value >>

A(self) == fork_35(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (promise_responses \X learners): proc_2(self))
           \/ (\E self \in (proposers \X learners): proc_3(self))
           \/ (\E self \in learners: L(self))
           \/ (\E self \in (acceptors \X proposers): proc_18(self))
           \/ (\E self \in ("P_par_8" \X {proposers}): proc_9(self))
           \/ (\E self \in (promise_responses \X proposers): proc_22(self))
           \/ (\E self \in ("P_par_10" \X {proposers}): proc_11(self))
           \/ (\E self \in ("P_par_6" \X {proposers}): proc_13(self))
           \/ (\E self \in (proposers \ { Head(Tail(self)) } \X proposers): proc_26(self))
           \/ (\E self \in ("P_par_14" \X {proposers}): proc_15(self))
           \/ (\E self \in proposers: P(self))
           \/ (\E self \in ("A_par_28" \X {acceptors}): proc_29(self))
           \/ (\E self \in ("A_par_30" \X {acceptors}): proc_31(self))
           \/ (\E self \in (proposers \X acceptors): proc_36(self))
           \/ (\E self \in acceptors: A(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
