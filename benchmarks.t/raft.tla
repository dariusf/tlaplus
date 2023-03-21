--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC, TLCExt, Json, InboxOutbox, Monitoring

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
\* CONSTANTS Follower, Candidate, Leader

\* A reserved value.
\* CONSTANTS Nil

\* Message types:
\* CONSTANTS RequestVoteRequest, RequestVoteResponse,
\*           AppendEntriesRequest, AppendEntriesResponse

----

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
\* VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
\* VARIABLE allLogs

\* VARIABLE lastComm
\* VARIABLE who

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* "none" if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
\* VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted>>

\* VARIABLE actions

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
\* Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

InSeq(x, xs) == x \in ToSet(xs)

\* this cannot be implemented if in/outboxes are sets
DuplicateMsg(m) ==
  \E s \in Server :
    /\ inbox[s] /= <<>>
    /\ InSeq(m, inbox[s])
    /\ inbox' = [inbox EXCEPT ![s] = Append(inbox[s], m)]

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitHistoryVars == \*/\ elections = {}
                   /\ actions = <<>>
                  \*  /\ allLogs   = {}
                  \*  /\ lastComm = <<>>
                   /\ who = "none"
                  \*  /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> "Follower"]
                  /\ votedFor    = [i \in Server |-> "none"]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
InitCommVars ==
  /\ inbox = [i \in Server |-> <<>>]
  /\ outbox = [i \in Server |-> <<>>]
  /\ inflight = <<>>

InitNormal ==
  \* /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitCommVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

Init ==
  /\ InitNormal

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = "Follower"]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    \* /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    \* /\ who' = i
    /\ UNCHANGED <<currentTerm, votedFor, log>>
    \* /\ UNCHANGED <<lastComm>>
    /\ UNCHANGED <<inboxOutboxVars>>
    /\ LogAction(<<"Restart", i>>)
    /\ LogActor(i)

Initialize(i) ==
  /\ state[i] = "Follower"
  /\ log[i] = <<>>
  \* etcd OMISSION 1. bump
  /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
  \* etcd OMISSION 2. nodes go through a series of configurations to set up the cluster before timing out. simplified version of cluster reconfiguration
  /\ log' = [log EXCEPT ![i] = log[i] \o
    <<[term |-> 2, value |-> 0],
      [term |-> 2, value |-> 0],
      [term |-> 2, value |-> 0]>>]
  \* etcd OMISSION 4
  /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> 3]]
  /\ UNCHANGED <<state, votedFor>>
  /\ UNCHANGED <<commitIndex>>
  /\ UNCHANGED <<candidateVars>>
  /\ UNCHANGED matchIndex
  /\ UNCHANGED <<inboxOutboxVars>>
  /\ LogAction(<<"Initialize", i>>)
  /\ LogActor(i)


\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {"Follower", "Candidate"}
              /\ state' = [state EXCEPT ![i] = "Candidate"]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              \* /\ votedFor' = [votedFor EXCEPT ![i] = "none"]
              \* etcd OMISSION 6
              /\
                \/ votedFor' = [votedFor EXCEPT ![i] = "none"]
                \/ votedFor' = [votedFor EXCEPT ![i] = i]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              \* etcd OMISSION 5
              /\
                \/ UNCHANGED nextIndex
                \/ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> nextIndex[i][j]+1]]
              \* OMISSION 3
              \* fix is to add a disjunct that allows servers to vote for themselves immediately
              \* /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\
                \/ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
                \/ votesGranted'   = [votesGranted EXCEPT ![i] = {i}]
              \* /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              \* /\ who' = i
              \* etcd OMISSION 7
              /\
                \/ UNCHANGED matchIndex
                \/ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![i] = Len(log[i])]]
              /\ UNCHANGED <<logVars>>
              /\ UNCHANGED <<inboxOutboxVars>>
              \* /\ UNCHANGED <<lastComm>>
              /\ LogAction(<<"Timeout", i>>)
              /\ LogActor(i)

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = "Candidate"
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> "RequestVoteRequest",
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ who' = i
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
    \* /\ UNCHANGED Receivable
    /\ LogAction(<<"RequestVote", i, j>>)
    /\ LogActor(i)

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    \* /\ who' = i
    /\ i /= j
    /\ state[i] = "Leader"
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN
       /\
        \* OMISSION 7
        \* it's okay to send the commitIndex immediately, instead of the more conservative lastEntry which we are replicating if it is < commitIndex
         \/ Send([mtype        |-> "AppendEntriesRequest",
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                \* mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
         \/ Send([mtype        |-> "AppendEntriesRequest",
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                \* mlog           |-> log[i],
                mcommitIndex   |-> commitIndex[i],
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
    /\ LogAction(<<"AppendEntries", i>>)
    /\ LogActor(i)

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    \* /\ who' = i
    /\ state[i] = "Candidate"
    \* /\ votesGranted[i] \in Quorum
    /\ Cardinality(votesGranted[i]) >= Cardinality(Server) \div 2 + 1
    /\ state'      = [state EXCEPT ![i] = "Leader"]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    \* etcd OMISSION 9
    /\
      \/ matchIndex' = [matchIndex EXCEPT ![i] =
                          [j \in Server |-> 0]]
      \/ matchIndex' = [matchIndex EXCEPT ![i] =
                          [j \in Server |-> IF i = j THEN matchIndex[i][j] ELSE 0]]
    \* /\ elections'  = elections \cup
    \*                      {[eterm     |-> currentTerm[i],
    \*                        eleader   |-> i,
    \*                        elog      |-> log[i],
    \*                        evotes    |-> votesGranted[i],
    \*                        evoterLog |-> <<>>
    \*                       \*  voterLog[i]
    \*                        ]}
    \* etcd OMISSION 10
    /\
      \/ log' = [log EXCEPT ![i] = Append(log[i], [term |-> currentTerm[i], value |-> 0])]
      \/ UNCHANGED log
    \* etcd OMISSION 11
    /\
      \/ UNCHANGED candidateVars
      \/
        /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
        /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ UNCHANGED <<currentTerm, votedFor>>
    /\ UNCHANGED commitIndex
    \* /\ UNCHANGED <<lastComm>>
    /\ UNCHANGED <<inboxOutboxVars>>
    /\ LogAction(<<"BecomeLeader", i>>)
    /\ LogActor(i)

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    \* /\ who' = i
    /\ state[i] = "Leader"
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, candidateVars,
                   leaderVars, commitIndex>>
    \* /\ UNCHANGED <<lastComm>>
    /\ UNCHANGED <<inboxOutboxVars>>
    /\ LogAction(<<"ClientRequest", i, v>>)
    /\ LogActor(i)

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    \* /\ who' = i
    /\ state[i] = "Leader"
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                \* Agree(index) \in Quorum
                                Cardinality(Agree(index)) >= Cardinality(Server) \div 2 + 1
                                }
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, log>>
    \* /\ UNCHANGED <<lastComm>>
    /\ UNCHANGED <<inboxOutboxVars>>
    /\ LogAction(<<"AdvanceCommitIndex", i>>)
    /\ LogActor(i)

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {"none", j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> "RequestVoteResponse",
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                \*  mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       \* /\ who' = i
       /\ UNCHANGED inflight
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>
       /\ LogAction(<<"HandleRequestVoteRequest", i, j, m>>)
       /\ LogActor(i)

SelfVote(i) ==
  \* /\ FALSE
  \* etcd OMISSION 3. a new transition to allow candidates to vote directly for themselves
  /\ state[i] = "Candidate"
  /\ votedFor' = [votedFor EXCEPT ![i] = i]
  /\ Send([mtype        |-> "RequestVoteResponse",
           mterm        |-> currentTerm[i],
           mvoteGranted |-> TRUE,
           msource      |-> i,
           mdest        |-> i])
  /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>
  /\ LogAction(<<"SelfVote", i>>)
  /\ LogActor(i)

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
       \* OMISSION 4
       \* fix is to allow servers to not count a granted vote.
       \* this should only apply when they are leader, because it's not needed.
       \* if it applies when they are not leader, it is slow but unsafe.
       \/ /\ m.mvoteGranted
          /\ state[i] = "Leader"
          /\ UNCHANGED votesGranted
          \* /\ voterLog' = [voterLog EXCEPT ![i] =
                              \* voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          \* /\ UNCHANGED <<votesGranted, voterLog>>
          /\ UNCHANGED <<votesGranted>>
    /\ Discard(m)
    \* /\ who' = i
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>
    /\ LogAction(<<"HandleRequestVoteResponse", i, j, m>>)
    /\ LogActor(i)

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       \* /\ who' = i
       /\ LogAction(<<"HandleAppendEntriesRequest", i, j, m>>)
       /\ LogActor(i)
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = "Follower"
                   /\ \lnot logOk
             /\ Reply([mtype           |-> "AppendEntriesResponse",
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = "Candidate"
             /\ state' = [state EXCEPT ![i] = "Follower"]
             /\ UNCHANGED <<currentTerm, votedFor, logVars>>
            \*  /\ UNCHANGED <<lastComm>>
             /\ UNCHANGED <<inboxOutboxVars>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = "Follower"
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                          \* OMISSION 8 bound commitIndex by our log length
                                              m.mcommitIndex]
                                              \* Min({m.mcommitIndex, Len(log[i])})]
                       /\ Reply([mtype           |-> "AppendEntriesResponse",
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log>>
                       /\ UNCHANGED inflight
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex>>
                      \*  /\ UNCHANGED <<lastComm>>
                       /\ UNCHANGED <<inboxOutboxVars>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED serverVars
                       \* OMISSION 6
                       \* allow changing commit index
                       \* /\ UNCHANGED commitIndex
                       /\
                         \/ UNCHANGED commitIndex
                         \* BUGFIX bound commitIndex by our log length
                         \/ commitIndex' = [commitIndex EXCEPT ![i] = Min({m.mcommitIndex, Len(log'[i])})]
                      \*  /\ UNCHANGED <<lastComm>>
                       \* OMISSION 5
                       \* allow sending a reply
                       \* /\ UNCHANGED commVars
                       /\
                        \/ UNCHANGED <<inboxOutboxVars>>
                        \/
                          /\ UNCHANGED inflight
                          /\ Reply([mtype           |-> "AppendEntriesResponse",
                                    mterm           |-> currentTerm[i],
                                    msuccess        |-> TRUE,
                                    mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                    msource         |-> i,
                                    mdest           |-> j],
                                    m)
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    \* /\ who' = i
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars>>
    /\ LogAction(<<"HandleAppendEntriesResponse", i, j, m>>)
    /\ LogActor(i)

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    \* /\ who' = i
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = "Follower"]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = "none"]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<candidateVars, logVars>>
    \* etcd OMISSION 8
    /\
      \/ UNCHANGED matchIndex
      \/ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![i] = Len(log[i])]]
    /\
      \/ UNCHANGED nextIndex
      \/ nextIndex' = [nextIndex EXCEPT ![i] = [j1 \in Server |-> nextIndex[i][j1]+1]]
    \* /\ UNCHANGED <<lastComm>>
    /\ UNCHANGED <<inboxOutboxVars>>
    \* /\ UNCHANGED actions
    /\ LogAction(<<"UpdateTerm", i, j, m>>)
    /\ LogActor(i)

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    \* /\ who' = i
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
    /\ UNCHANGED actions
    /\ LogAction(<<"DropStaleResponse", i, j, m>>)
    /\ LogActor(i)

\* Receive a message.
ReceiveMsg(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m) \* TODO should this be conj?
       \/ /\ m.mtype = "RequestVoteRequest"
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = "RequestVoteResponse"
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = "AppendEntriesRequest"
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = "AppendEntriesResponse"
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
\* we don't want to add to outbox as this is observable
    \* /\ Send(m)
    /\ DuplicateMsg(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
    /\ UNCHANGED outbox
    /\ UNCHANGED inflight
    /\ LogAction(<<"DuplicateMessage", m>>)
    /\ LogActor("Network")

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
    /\ LogAction(<<"DropMessage", m>>)
    /\ LogActor("Network")

----
\* Defines how the variables may transition.
Next ==
  \* \/ \E i \in Server : Restart(i)
  \* \/ Timeout("s1")
  \/ \E i \in Server : Timeout(i)
  \* etcd OMISSIONs
  \* \/ \E i \in Server : SelfVote(i)
  \* \/ \E i \in Server : Initialize(i)
  \/ \E i,j \in Server : RequestVote(i, j)
  \/ \E i \in Server : BecomeLeader(i)
  \* \/ BecomeLeader("s1")
  \/ \E i \in Server, v \in Value : ClientRequest(i, v)
  \/ \E i \in Server : AdvanceCommitIndex(i)
  \/ \E i,j \in Server : AppendEntries(i, j)
  \/
    LET msgs == MsgsIn(inbox) IN
    \E i \in 1..Len(msgs) : ReceiveMsg(msgs[i])
  \*  \/ \E m \in Receivable : DuplicateMessage(m)
  \*  \/ \E m \in Receivable : DropMessage(m)
  \/ \E s \in Server : \E i \in 1..Len(outbox[s]) :
    /\ NetworkTakeMessage(outbox[s][i])
    /\ UNCHANGED vars
  \/ \E i \in 1..Len(inflight) :
    /\ NetworkDeliverMessage(inflight[i])
    /\ UNCHANGED vars
    \* History variable that tracks every log ever:
    \* /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

Alias == [
  currentTerm |-> currentTerm
  , state |-> state
  , inbox |-> inbox
  , outbox |-> outbox
  , actions |-> actions
  , inflight |-> inflight
  \* , s1Inbox |-> s1Inbox
  \* , s1Outbox |-> s1Outbox
  \* , s2Inbox |-> s2Inbox
  \* , s2Outbox |-> s2Outbox
  \* , s3Inbox |-> s3Inbox
  \* , s3Outbox |-> s3Outbox
]

TargetLength == ~
  TLCGet("level") > 10

TargetSomeLeader == ~
  \E n \in Server : state[n] = "Leader"

DesiredHist ==
LET rv2 == [mtype |-> "RequestVoteRequest", mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> "s1", mdest |-> "s2"]
    rv3 == [mtype |-> "RequestVoteRequest", mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> "s1", mdest |-> "s3"]
    rvr2 == [mtype |-> "RequestVoteResponse", mterm |-> 2, mvoteGranted |-> TRUE, msource |-> "s2", mdest |-> "s1"]
    rvr3 == [mtype |-> "RequestVoteResponse", mterm |-> 2, mvoteGranted |-> TRUE, msource |-> "s3", mdest |-> "s1"]
IN
<<
  <<"Timeout", "s1">>
  , <<"RequestVote", "s1", "s2">>
  , <<"RequestVote", "s1", "s3">>
  , <<"NetworkTakeMessage", rv2>>
  , <<"NetworkTakeMessage", rv3>>
  , <<"NetworkDeliverMessage", rv2>>
  , <<"NetworkDeliverMessage", rv3>>
  , <<"UpdateTerm", "s2", "s1", rv2>>
  , <<"HandleRequestVoteRequest", "s2", "s1", rv2>>
  , <<"UpdateTerm", "s3", "s1", rv3>>
  , <<"HandleRequestVoteRequest", "s3", "s1", rv3>>
  , <<"NetworkTakeMessage", rvr2>>
  , <<"NetworkTakeMessage", rvr3>>
  , <<"NetworkDeliverMessage", rvr2>>
  , <<"NetworkDeliverMessage", rvr3>>
  , <<"HandleRequestVoteResponse", "s1", "s2", rvr2>>
  , <<"HandleRequestVoteResponse", "s1", "s3", rvr3>>
  , <<"BecomeLeader", "s1">>
>>

ConstrHist ==
  \* level 1 is the initial state, and at that point actions is empty
  LET i == TLCGet("level") - 1 IN
  1 <= i /\ i <= Len(DesiredHist) =>
    actions[i] = DesiredHist[i]

TargetHist == ~
  LET i == TLCGet("level") - 1 IN
  /\ i = Len(DesiredHist)
  /\ actions[i] = DesiredHist[i]

Post ==
    LET t1 == ToTrace(CounterExample) IN
    /\ JsonSerialize("trace.json", t1)

===============================================================================

\* Changelog:
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
