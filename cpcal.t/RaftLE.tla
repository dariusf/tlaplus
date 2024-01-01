--------------------- MODULE RaftLE ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS s1, s2, s3

(* --algorithm RaftLE {
  variables
    servers = {s1, s2, s3};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (S \in servers)
      variables
        role = "follower",
        votes = {},
        voted_for = <<>>,
        term = 0,
        grant = FALSE;
  {
    par { \* Handle timeouts
      all (s \in servers) {
        while (TRUE) {
          await role = "follower";
          role := "candidate";
        }
      }
    } and { \* Start an election
      all (s \in servers) {
        while (TRUE) {
          await role = "candidate";
          votes := {};
          term := term + 1;
          task servers, "s" {
            par {
              \* Vote for ourselves too
              all (t \in servers) {
                Transmit(s, t, [Type |-> "RequestVote", Term |-> term[s]]);
                \* msg
                \* Drop stale messages
                if (msg.Term <= term[t]) {
                  grant[t] := TRUE;
                  if (grant[t]) {
                    voted_for[t] := <<t>>;
                  };
                  Transmit(t, s, [Type |-> "RequestVoteResp", Term |-> term[t], Grant |-> grant[t]]);
                  \* Drop stale messages
                  if (msg.Term = term[s]) {
                    if (msg.Granted) {
                      votes[s] := votes[s] \union {t};
                    }
                  }
                }
              }
            } and {
              await Cardinality(votes) > Quorum(servers);
              role := "leader";
            } and {
              cancel "s";
            }
          } \* end task
        } \* end while
      }
    } and {
      \* ...
      skip;
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "2fcce48c" /\ chksum(tla) = "660f78cb")
VARIABLES servers, messages, cancelled_s, pc, role, votes, voted_for, term, 
          grant

vars == << servers, messages, cancelled_s, pc, role, votes, voted_for, term, 
           grant >>

ProcSet == (("S_par_3" \X {servers})) \cup ((servers \ { Head(Tail(self)) } \X servers)) \cup (("S_par_5" \X {servers})) \cup (("S_par_15" \X {servers})) \cup ((servers \ { Head(Tail(self)) } \X servers)) \cup (("S_par_17" \X {servers})) \cup (("S_par_13" \X {servers})) \cup (("S_par_21" \X {servers})) \cup (("S_par_27" \X {servers})) \cup (("S_par_29" \X {servers})) \cup (("S_par_11" \X {servers})) \cup ((servers \ { Head(Tail(self)) } \X servers)) \cup (("S_par_25" \X {servers})) \cup (("S_par_1" \X {servers})) \cup (("S_par_9" \X {servers})) \cup (servers)

Init == (* Global variables *)
        /\ servers = {s1, s2, s3}
        /\ messages = {}
        /\ cancelled_s = FALSE
        (* Process S *)
        /\ role = [self \in servers |-> "follower"]
        /\ votes = [self \in servers |-> {}]
        /\ voted_for = [self \in servers |-> <<>>]
        /\ term = [self \in servers |-> 0]
        /\ grant = [self \in servers |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in ("S_par_3" \X {servers}) -> "Lbl_1"
                                        [] self \in (servers \ { Head(Tail(self)) } \X servers) -> "Lbl_3"
                                        [] self \in ("S_par_5" \X {servers}) -> "Lbl_5"
                                        [] self \in ("S_par_15" \X {servers}) -> "Lbl_6"
                                        [] self \in (servers \ { Head(Tail(self)) } \X servers) -> "Lbl_7"
                                        [] self \in ("S_par_17" \X {servers}) -> "Lbl_8"
                                        [] self \in ("S_par_13" \X {servers}) -> "Lbl_9"
                                        [] self \in ("S_par_21" \X {servers}) -> "Lbl_10"
                                        [] self \in ("S_par_27" \X {servers}) -> "Lbl_11"
                                        [] self \in ("S_par_29" \X {servers}) -> "Lbl_12"
                                        [] self \in ("S_par_11" \X {servers}) -> "Lbl_13"
                                        [] self \in (servers \ { Head(Tail(self)) } \X servers) -> "Lbl_15"
                                        [] self \in ("S_par_25" \X {servers}) -> "Lbl_17"
                                        [] self \in ("S_par_1" \X {servers}) -> "Lbl_18"
                                        [] self \in ("S_par_9" \X {servers}) -> "Lbl_19"
                                        [] self \in servers -> "par_0"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ pc[Head(Tail(self))] = "par_2"
               /\ pc' = [pc EXCEPT ![self] = "Lbl_2"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ role[self] = "follower"
               /\ role' = [role EXCEPT ![self] = "candidate"]
               /\ pc' = [pc EXCEPT ![self] = "Lbl_2"]
               /\ UNCHANGED << servers, messages, cancelled_s, votes, 
                               voted_for, term, grant >>

proc_4(self) == Lbl_1(self) \/ Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ pc[Head(Tail(self))] = "fork_36"
               /\ pc' = [pc EXCEPT ![self] = "Lbl_4"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

Lbl_4(self) == /\ pc[self] = "Lbl_4"
               /\ role[self] = "follower"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Lbl_4"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

proc_37(self) == Lbl_3(self) \/ Lbl_4(self)

Lbl_5(self) == /\ pc[self] = "Lbl_5"
               /\ pc[Head(Tail(self))] = "par_2"
               /\ pc' = [pc EXCEPT ![self] = "fork_36"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

fork_36(self) == /\ pc[self] = "fork_36"
                 /\ \A s \in (servers \ { Head(Tail(self)) } \X servers) : pc[s] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                 voted_for, term, grant >>

proc_6(self) == Lbl_5(self) \/ fork_36(self)

Lbl_6(self) == /\ pc[self] = "Lbl_6"
               /\ pc[Head(Tail(self))] = "par_14"
               /\ pc' = [pc EXCEPT ![self] = "comm_38"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

comm_38(self) == /\ pc[self] = "comm_38"
                 /\ messages' = (messages \union {[To |-> Head(Tail(self)), From |-> Head(Tail(self)), Type |-> ([ Type |-> "RequestVote" , Term |-> term[self] ])]})
                 /\ pc' = [pc EXCEPT ![self] = "comm_39"]
                 /\ UNCHANGED << servers, cancelled_s, role, votes, voted_for, 
                                 term, grant >>

comm_39(self) == /\ pc[self] = "comm_39"
                 /\ [To |-> Head(Tail(self)), From |-> Head(Tail(self)), Type |-> ([ Type |-> "RequestVote" , Term |-> term[self] ])] \in messages
                 /\ IF msg.Term <= term[self][t]
                       THEN /\ grant' = [grant EXCEPT ![self] = TRUE]
                            /\ IF grant'[self][t]
                                  THEN /\ voted_for' = [voted_for EXCEPT ![self] = << Head(Tail(self))>>]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED voted_for
                            /\ pc' = [pc EXCEPT ![self] = "comm_40"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << voted_for, grant >>
                 /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                 term >>

comm_40(self) == /\ pc[self] = "comm_40"
                 /\ messages' = (messages \union {[To |-> Head(Tail(self)), From |-> Head(Tail(self)), Type |-> ([ Type |-> "RequestVoteResp" , Term |-> term[self] , Grant |-> grant[self] ])]})
                 /\ pc' = [pc EXCEPT ![self] = "comm_41"]
                 /\ UNCHANGED << servers, cancelled_s, role, votes, voted_for, 
                                 term, grant >>

comm_41(self) == /\ pc[self] = "comm_41"
                 /\ [To |-> Head(Tail(self)), From |-> Head(Tail(self)), Type |-> ([ Type |-> "RequestVoteResp" , Term |-> term[self] , Grant |-> grant[self] ])] \in messages
                 /\ IF msg.Term = term[self][s]
                       THEN /\ IF msg.Granted
                                  THEN /\ votes' = [votes EXCEPT ![self] = votes[self] \union { Head(Tail(self))}]
                                  ELSE /\ TRUE
                                       /\ votes' = votes
                       ELSE /\ TRUE
                            /\ votes' = votes
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << servers, messages, cancelled_s, role, 
                                 voted_for, term, grant >>

proc_16(self) == Lbl_6(self) \/ comm_38(self) \/ comm_39(self)
                    \/ comm_40(self) \/ comm_41(self)

Lbl_7(self) == /\ pc[self] = "Lbl_7"
               /\ pc[Head(Tail(self))] = "fork_42"
               /\ pc' = [pc EXCEPT ![self] = "comm_44"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

comm_44(self) == /\ pc[self] = "comm_44"
                 /\ messages' = (messages \union {[To |-> Head(self), From |-> (Head(Tail(self))), Type |-> ([ Type |-> "RequestVote" , Term |-> term[self] ])]})
                 /\ IF msg.Term <= term[self][t]
                       THEN /\ pc' = [pc EXCEPT ![self] = "comm_45"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << servers, cancelled_s, role, votes, voted_for, 
                                 term, grant >>

comm_45(self) == /\ pc[self] = "comm_45"
                 /\ [To |-> (Head(Tail(self))), From |-> Head(self), Type |-> ([ Type |-> "RequestVoteResp" , Term |-> term[self] , Grant |-> grant[self] ])] \in messages
                 /\ IF msg.Term = term[self][s]
                       THEN /\ IF msg.Granted
                                  THEN /\ votes' = [votes EXCEPT ![self] = votes[self] \union { Head(self)}]
                                  ELSE /\ TRUE
                                       /\ votes' = votes
                       ELSE /\ TRUE
                            /\ votes' = votes
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << servers, messages, cancelled_s, role, 
                                 voted_for, term, grant >>

proc_43(self) == Lbl_7(self) \/ comm_44(self) \/ comm_45(self)

Lbl_8(self) == /\ pc[self] = "Lbl_8"
               /\ pc[Head(Tail(self))] = "par_14"
               /\ pc' = [pc EXCEPT ![self] = "fork_42"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

fork_42(self) == /\ pc[self] = "fork_42"
                 /\ \A t \in (servers \ { Head(Tail(self)) } \X servers) : pc[t] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                 voted_for, term, grant >>

proc_18(self) == Lbl_8(self) \/ fork_42(self)

Lbl_9(self) == /\ pc[self] = "Lbl_9"
               /\ pc[Head(Tail(self))] = "par_12"
               /\ pc' = [pc EXCEPT ![self] = "par_14"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

par_14(self) == /\ pc[self] = "par_14"
                /\ \A v_19 \in ({"S_par_15", "S_par_17"} \X {servers}) : pc[v_19] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

proc_20(self) == Lbl_9(self) \/ par_14(self)

Lbl_10(self) == /\ pc[self] = "Lbl_10"
                /\ pc[Head(Tail(self))] = "par_12"
                /\ Cardinality ( votes[self] ) > Quorum ( servers )
                /\ role' = [role EXCEPT ![self] = "leader"]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, messages, cancelled_s, votes, 
                                voted_for, term, grant >>

proc_22(self) == Lbl_10(self)

Lbl_11(self) == /\ pc[self] = "Lbl_11"
                /\ pc[Head(Tail(self))] = "par_26"
                /\ pc' = [pc EXCEPT ![self] = "comm_46"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

comm_46(self) == /\ pc[self] = "comm_46"
                 /\ [To |-> Head(Tail(self)), From |-> s, Type |-> ([ Type |-> "RequestVote" , Term |-> term[self] ])] \in messages
                 /\ IF msg.Term <= term[self][t]
                       THEN /\ grant' = [grant EXCEPT ![self] = TRUE]
                            /\ IF grant'[self][t]
                                  THEN /\ voted_for' = [voted_for EXCEPT ![self] = << Head(Tail(self))>>]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED voted_for
                            /\ pc' = [pc EXCEPT ![self] = "comm_47"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << voted_for, grant >>
                 /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                 term >>

comm_47(self) == /\ pc[self] = "comm_47"
                 /\ messages' = (messages \union {[To |-> s, From |-> Head(Tail(self)), Type |-> ([ Type |-> "RequestVoteResp" , Term |-> term[self] , Grant |-> grant[self] ])]})
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << servers, cancelled_s, role, votes, voted_for, 
                                 term, grant >>

proc_28(self) == Lbl_11(self) \/ comm_46(self) \/ comm_47(self)

Lbl_12(self) == /\ pc[self] = "Lbl_12"
                /\ pc[Head(Tail(self))] = "par_26"
                /\ Cardinality ( votes[self] ) > Quorum ( servers )
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

proc_30(self) == Lbl_12(self)

Lbl_13(self) == /\ pc[self] = "Lbl_13"
                /\ pc[Head(Tail(self))] = "par_10"
                /\ pc' = [pc EXCEPT ![self] = "Lbl_14"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

Lbl_14(self) == /\ pc[self] = "Lbl_14"
                /\ role[self] = "candidate"
                /\ votes' = [votes EXCEPT ![self] = { }]
                /\ term' = [term EXCEPT ![self] = term[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "par_12"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, 
                                voted_for, grant >>

par_12(self) == /\ pc[self] = "par_12"
                /\ \A v_23 \in ({"S_par_13", "S_par_21"} \X {servers}) : pc[v_23] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Lbl_14"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

proc_24(self) == Lbl_13(self) \/ Lbl_14(self) \/ par_12(self)

Lbl_15(self) == /\ pc[self] = "Lbl_15"
                /\ pc[Head(Tail(self))] = "fork_48"
                /\ pc' = [pc EXCEPT ![self] = "Lbl_16"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

Lbl_16(self) == /\ pc[self] = "Lbl_16"
                /\ role[self] = "candidate"
                /\ TRUE
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "par_26"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

par_26(self) == /\ pc[self] = "par_26"
                /\ \A v_31 \in ( { "S_par_27" , "S_par_29" } \X { servers } ) : pc [ v_31 ] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Lbl_16"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

proc_49(self) == Lbl_15(self) \/ Lbl_16(self) \/ par_26(self)

Lbl_17(self) == /\ pc[self] = "Lbl_17"
                /\ pc[Head(Tail(self))] = "par_10"
                /\ pc' = [pc EXCEPT ![self] = "fork_48"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

fork_48(self) == /\ pc[self] = "fork_48"
                 /\ \A s \in (servers \ { Head(Tail(self)) } \X servers) : pc[s] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                 voted_for, term, grant >>

proc_32(self) == Lbl_17(self) \/ fork_48(self)

Lbl_18(self) == /\ pc[self] = "Lbl_18"
                /\ pc[Head(Tail(self))] = "par_0"
                /\ pc' = [pc EXCEPT ![self] = "par_2"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

par_2(self) == /\ pc[self] = "par_2"
               /\ \A v_7 \in ({"S_par_3", "S_par_5"} \X {servers}) : pc[v_7] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

proc_8(self) == Lbl_18(self) \/ par_2(self)

Lbl_19(self) == /\ pc[self] = "Lbl_19"
                /\ pc[Head(Tail(self))] = "par_0"
                /\ pc' = [pc EXCEPT ![self] = "par_10"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

par_10(self) == /\ pc[self] = "par_10"
                /\ \A v_33 \in ({"S_par_11", "S_par_25"} \X {servers}) : pc[v_33] = "Done"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                                voted_for, term, grant >>

proc_34(self) == Lbl_19(self) \/ par_10(self)

par_0(self) == /\ pc[self] = "par_0"
               /\ \A v_35 \in ({"S_par_1", "S_par_9"} \X {servers}) : pc[v_35] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << servers, messages, cancelled_s, role, votes, 
                               voted_for, term, grant >>

S(self) == par_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ("S_par_3" \X {servers}): proc_4(self))
           \/ (\E self \in (servers \ { Head(Tail(self)) } \X servers): proc_37(self))
           \/ (\E self \in ("S_par_5" \X {servers}): proc_6(self))
           \/ (\E self \in ("S_par_15" \X {servers}): proc_16(self))
           \/ (\E self \in (servers \ { Head(Tail(self)) } \X servers): proc_43(self))
           \/ (\E self \in ("S_par_17" \X {servers}): proc_18(self))
           \/ (\E self \in ("S_par_13" \X {servers}): proc_20(self))
           \/ (\E self \in ("S_par_21" \X {servers}): proc_22(self))
           \/ (\E self \in ("S_par_27" \X {servers}): proc_28(self))
           \/ (\E self \in ("S_par_29" \X {servers}): proc_30(self))
           \/ (\E self \in ("S_par_11" \X {servers}): proc_24(self))
           \/ (\E self \in (servers \ { Head(Tail(self)) } \X servers): proc_49(self))
           \/ (\E self \in ("S_par_25" \X {servers}): proc_32(self))
           \/ (\E self \in ("S_par_1" \X {servers}): proc_8(self))
           \/ (\E self \in ("S_par_9" \X {servers}): proc_34(self))
           \/ (\E self \in servers: S(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

==================================================================
