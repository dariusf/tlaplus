--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC, TLCExt, Json

ToSet(s) == { s[i] : i \in DOMAIN s }

MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]


FoldFunction(op(_,_), base, fun) ==
  MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s: CHOOSE x \in s : TRUE, DOMAIN fun)

FoldSeq(op(_, _), base, seq) == 
  FoldFunction(op, base, seq)

Remove(s, e) ==
    SelectSeq(s, LAMBDA t: t # e)

RemoveAt(s, i) == 
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

IsPrefix(s, t) ==
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))

IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

SetToSeq(S) == 
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

\* The set of server IDs
CONSTANTS Server

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
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
\* VARIABLE messages

VARIABLES outbox, inbox
VARIABLES inflight

\* VARIABLES s1Outbox, s1Inbox
\* VARIABLES s2Outbox, s2Inbox
\* VARIABLES s3Outbox, s3Inbox

commVars == <<
  \* s1Outbox, s1Inbox
  \* , s2Outbox, s2Inbox
  \* , s3Outbox, s3Inbox
  outbox, inbox, inflight
>>

\* Receivable == s1Inbox \union s2Inbox \union s3Inbox
\* Sendable == s1Outbox \union s2Outbox \union s3Outbox

\* Receivable == ToSet(s1Inbox) \union ToSet(s2Inbox) \union ToSet(s3Inbox)
\* Sendable == ToSet(s1Outbox) \union ToSet(s2Outbox) \union ToSet(s3Outbox)

MsgsIn(box) == FoldSeq(LAMBDA c,t: box[c] \o t, <<>>, SetToSeq(Server))

\* Receivable == s1Inbox \o s2Inbox \o s3Inbox
\* Sendable == s1Outbox \o s2Outbox \o s3Outbox

\* inboxVars == <<s1Inbox, s2Inbox, s3Inbox>>
inboxVars == <<inbox>>

\* outboxVars == <<s1Outbox, s2Outbox, s3Outbox>>
outboxVars == <<outbox>>

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
VARIABLE who

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

VARIABLE actions

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
\* who,
\* allLogs,

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
\* Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* SendM(sender, m) ==
\*   IF sender = "s1" THEN
\*     /\ s1Outbox' = Append(s1Outbox, m)
\*     \* /\ s1Outbox' = s1Outbox \union {m}
\*     /\ UNCHANGED s2Outbox
\*     /\ UNCHANGED s3Outbox
\*   ELSE IF sender = "s2" THEN
\*     /\ UNCHANGED s1Outbox
\*     /\ s2Outbox' = Append(s2Outbox, m)
\*     \* /\ s2Outbox' = s2Outbox \union {m}
\*     /\ UNCHANGED s3Outbox
\*   ELSE
\*     /\ UNCHANGED s1Outbox
\*     /\ UNCHANGED s2Outbox
\*     /\ s3Outbox' = Append(s3Outbox, m)
\*     \* /\ s3Outbox' = s3Outbox \union {m}

SendM(sender, m) ==
  outbox' = [outbox EXCEPT ![sender] = Append(outbox[sender], m)]

\* Add a message to the bag of messages.
Send(m) ==
  SendM(m.msource, m)
  \* /\ messages' = WithMessage(m, messages)
  \* /\ lastComm' = <<[who |-> m.msource, msg |-> m]>>

InSeq(x, xs) == x \in ToSet(xs)

\* \* this cannot be implemented if in/outboxes are sets
\* DuplicateMsg(m) ==
\*   \/
\*     /\ s1Inbox /= <<>>
\*     /\ InSeq(m, s1Inbox)
\*     /\ s1Inbox' = Append(s1Inbox, m)
\*   \/
\*     /\ s2Inbox /= <<>>
\*     /\ InSeq(m, s2Inbox)
\*     /\ s2Inbox' = Append(s2Inbox, m)
\*   \/
\*     /\ s3Inbox /= <<>>
\*     /\ InSeq(m, s3Inbox)
\*     /\ s3Inbox' = Append(s3Inbox, m)

\* this cannot be implemented if in/outboxes are sets
DuplicateMsg(m) ==
  \E s \in Server :
    /\ inbox[s] /= <<>>
    /\ InSeq(m, inbox[s])
    /\ inbox' = [inbox EXCEPT ![s] = Append(inbox[s], m)]

\* RecvM(recipient, m) ==
\*   IF recipient = "s1" THEN
\*     /\ m \in ToSet(s1Inbox)
\*     /\
\*       \* LET e == CHOOSE x \in s1Inbox : TRUE IN
\*       \* s1Inbox' = s1Inbox \ {e}
\*       \* LET e == Head(s1Inbox) IN
\*       \* s1Inbox' = Tail(s1Inbox)
\*       s1Inbox' = Remove(s1Inbox, m)
\*     /\ UNCHANGED s2Inbox
\*     /\ UNCHANGED s3Inbox
\*   ELSE IF recipient = "s2" THEN
\*     /\ UNCHANGED s1Inbox
\*     /\ m \in ToSet(s2Inbox)
\*     /\ s2Inbox' = Remove(s2Inbox, m)
\*     /\ UNCHANGED s3Inbox
\*   ELSE
\*     /\ UNCHANGED s1Inbox
\*     /\ UNCHANGED s2Inbox
\*     /\ m \in ToSet(s3Inbox)
\*     /\ s3Inbox' = Remove(s3Inbox, m)

RecvM(recipient, m) ==
  /\ m \in ToSet(inbox[recipient])
  /\ inbox' = [inbox EXCEPT ![recipient] = Remove(inbox[recipient], m)]

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) ==
  RecvM(m.mdest, m)
  \* /\ messages' = WithoutMessage(m, messages)
  \* /\ lastComm' = <<[who |-> m.mdest, msg |-> m]>>

\* Combination of Send and Discard
Reply(response, request) ==
  /\ Discard(request)
  /\ Send(response)
  \* /\ messages' = WithoutMessage(request, WithMessage(response, messages))
  \* /\ lastComm' = <<[who |-> request.mdest, msg |-> request], [who |-> response.msource, msg |-> response]>>

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

LogAction(a) ==
  /\ actions' = Append(actions, a)
  \* /\ actions' = a

LogActor(w) ==
  /\ who' = w
  \* /\ who' = Append(who, w)

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
  \* /\ s1Inbox = {}
  \* /\ s1Outbox = {}
  \* /\ s2Inbox = {}
  \* /\ s2Outbox = {}
  \* /\ s3Inbox = {}
  \* /\ s3Outbox = {}

  \* /\ s1Inbox = <<>>
  \* /\ s1Outbox = <<>>
  \* /\ s2Inbox = <<>>
  \* /\ s2Outbox = <<>>
  \* /\ s3Inbox = <<>>
  \* /\ s3Outbox = <<>>

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
    /\ UNCHANGED commVars
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
  /\ UNCHANGED <<state, votedFor>>
  /\ UNCHANGED <<commitIndex>>
  /\ UNCHANGED <<candidateVars, leaderVars>>
  /\ UNCHANGED <<commVars>>
  /\ LogAction(<<"Initialize", i>>)
  /\ LogActor(i)


\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {"Follower", "Candidate"}
              /\ state' = [state EXCEPT ![i] = "Candidate"]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = "none"]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              \* OMISSION 3
              \* fix is to add a disjunct that allows servers to vote for themselves immediately
              \* /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\
                \/ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
                \/ votesGranted'   = [votesGranted EXCEPT ![i] = {i}]
              \* /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              \* /\ who' = i
              /\ UNCHANGED <<leaderVars, logVars>>
              /\ UNCHANGED commVars
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
    /\ UNCHANGED <<inboxVars>>
    /\ UNCHANGED <<inflight>>
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
    /\ UNCHANGED <<inboxVars>>
    /\ UNCHANGED <<inflight>>
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
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    \* /\ elections'  = elections \cup
    \*                      {[eterm     |-> currentTerm[i],
    \*                        eleader   |-> i,
    \*                        elog      |-> log[i],
    \*                        evotes    |-> votesGranted[i],
    \*                        evoterLog |-> <<>>
    \*                       \*  voterLog[i]
    \*                        ]}
    /\ UNCHANGED <<currentTerm, votedFor, candidateVars, logVars>>
    \* /\ UNCHANGED <<lastComm>>
    /\ UNCHANGED commVars
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
    /\ UNCHANGED commVars
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
    /\ UNCHANGED commVars
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
  /\ UNCHANGED <<inboxVars>>
  /\ UNCHANGED <<inflight>>
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
    /\ UNCHANGED <<outboxVars>>
    /\ UNCHANGED <<inflight>>
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
             /\ UNCHANGED commVars
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
                       /\ UNCHANGED commVars
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
                        \/ UNCHANGED commVars
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
    /\ UNCHANGED outboxVars
    /\ UNCHANGED <<inflight>>
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
    /\ UNCHANGED <<candidateVars, leaderVars, logVars>>
    \* /\ UNCHANGED <<lastComm>>
    /\ UNCHANGED commVars
    \* /\ UNCHANGED actions
    /\ LogAction(<<"UpdateTerm", i, j, m>>)
    /\ LogActor(i)

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    \* /\ who' = i
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
    /\ UNCHANGED outboxVars
    /\ UNCHANGED <<inflight>>
    /\ UNCHANGED actions
    /\ LogAction(<<"DropStaleResponse", i, j, m>>)
    /\ LogActor(i)

\* Receive a message.
Receive(m) ==
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
    /\ UNCHANGED <<outboxVars>>
    /\ UNCHANGED <<inflight>>
    /\ LogAction(<<"DuplicateMessage", m>>)
    /\ LogActor("Network")

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
    /\ UNCHANGED <<outboxVars>>
    /\ UNCHANGED <<inflight>>
    /\ LogAction(<<"DropMessage", m>>)
    /\ LogActor("Network")

\* NetworkDelivery ==
\*   /\
\*     \* \/ s1Outbox /= {}
\*     \* \/ s2Outbox /= {}
\*     \* \/ s3Outbox /= {}
\*     \/ s1Outbox /= <<>>
\*     \/ s2Outbox /= <<>>
\*     \/ s3Outbox /= <<>>
\*   /\ s1Outbox' = <<>>
\*   /\ s2Outbox' = <<>>
\*   /\ s3Outbox' = <<>>
\*   \* /\ s1Outbox' = {}
\*   \* /\ s2Outbox' = {}
\*   \* /\ s3Outbox' = {}
\*   \* /\ s1Inbox' = { m \in Sendable : m.mdest = "s1" } \union s1Inbox
\*   \* /\ s2Inbox' = { m \in Sendable : m.mdest = "s2" } \union s2Inbox
\*   \* /\ s3Inbox' = { m \in Sendable : m.mdest = "s3" } \union s3Inbox
\*   /\ s1Inbox' = SetToSeq({ m \in Sendable : m.mdest = "s1" }) \o s1Inbox
\*   /\ s2Inbox' = SetToSeq({ m \in Sendable : m.mdest = "s2" }) \o s2Inbox
\*   /\ s3Inbox' = SetToSeq({ m \in Sendable : m.mdest = "s3" }) \o s3Inbox
\*   /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
\*   /\ LogAction("Network")

\* deliver everything at once
\* this is unused
NetworkDelivery ==
  /\ \E s \in Server : outbox[s] /= <<>>
  /\ outbox' = [s \in Server |-> <<>>]
  /\ inbox' = [s \in Server |-> inbox[s] \o SelectSeq(MsgsIn(outbox), LAMBDA m : m.mdest = s)]
  /\ UNCHANGED inflight
  /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
  \* we don't capture args here, but it's unlikely we'll have to repair this
  /\ LogAction(<<"Network">>)
  /\ LogActor("Network")

NetworkTakeMessage(s) ==
  /\ outbox[s] /= <<>>
  /\ outbox' = [s1 \in Server |-> <<>>]
  /\ inflight' = inflight \o MsgsIn(outbox)
  /\ UNCHANGED inbox
  /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
  /\ LogAction(<<"NetworkTakeMessage", MsgsIn(outbox)>>)
  /\ LogActor("Network")

\* this is unused
NetworkDeliverMessage ==
  /\ inflight /= <<>>
  /\ inbox' = [s \in Server |-> SelectSeq(inflight, LAMBDA m : m.mdest = s)]
  /\ inflight' = <<>>
  /\ UNCHANGED outbox
  /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
  /\ LogAction(<<"NetworkDeliverMessage">>)
  /\ LogActor("Network")

\* this delivers only one message at a time, which corresponds to what impls see
NetworkDeliverMessageSlow(r, i) ==
  /\ inflight /= <<>>
  /\ inflight[i].mdest = r
  /\ inbox' = [inbox EXCEPT ![r] = Append(inbox[r], inflight[i])]
  /\ inflight' = RemoveAt(inflight, i)
  /\ LogAction(<<"NetworkDeliverMessageSlow", inflight[i]>>)
  /\ LogActor("Network")
  /\ UNCHANGED outbox
  /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
Next == \*/\
          \* \/ \E i \in Server : Restart(i)
           \* \/ Timeout("s1")
           \/ \E i \in Server : Timeout(i)
           \/ \E i \in Server : SelfVote(i)
           \/ \E i \in Server : Initialize(i)
           \/ \E i,j \in Server : RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \* \/ BecomeLeader("s1")
           \/ \E i \in Server, v \in Value : ClientRequest(i, v)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : AppendEntries(i, j)
           \/
             LET msgs == MsgsIn(inbox) IN
             \E i \in 1..Len(msgs) : Receive(msgs[i])
          \*  \/ \E m \in Receivable : DuplicateMessage(m)
          \*  \/ \E m \in Receivable : DropMessage(m)
          \*  \/ NetworkDelivery
           \/ \E s \in Server : NetworkTakeMessage(s)
           \* \/ NetworkDeliverMessage
           \/ \E r \in Server : \E i \in 1..Len(inflight) :
             NetworkDeliverMessageSlow(r, i)
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

\* TargetTest1 == ~
\*   \* /\ Len(lastComm) > 1
\*   /\ Len(lastComm) = 1
\*   /\ lastComm[1].msg.mtype = "RequestVoteResponse"
\*   /\ lastComm[1].who /= lastComm[1].msg.msource
\*   /\ lastComm[1].who = "s3"

  \* TLCGet("level") > 3
  \* /\ currentTerm["s3"] = 2
  \* Cardinality(messages) = 3
  \* /\ PrintT(DOMAIN messages)
  \* /\ PrintT([mtype |-> "RequestVoteResponse", mterm |-> 1, mvoteGranted |-> TRUE, msource |-> "s1", mdest |-> "s3"] = [mtype |-> "RequestVoteResponse", mterm |-> 1, mvoteGranted |-> TRUE, msource |-> "s1", mdest |-> "s3"])
  \* /\ [mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, mtype |-> "RequestVoteRequest", msource |-> "s3", mdest |-> "s2"] \in DOMAIN messages
  \* /\ lastComm = <<[who |-> "s3", msg |-> [mtype |-> "RequestVoteResponse", mterm |-> 1, mvoteGranted |-> TRUE, msource |-> "s1", mdest |-> "s3"]]>>
  \* /\ lastComm = <<[who |-> "s3", msg |-> [mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, mtype |-> "RequestVoteRequest", msource |-> "s3", mdest |-> "s2"]]>>
  \* /\ [mtype |-> "RequestVoteResponse", mterm |-> 1, mvoteGranted |-> TRUE, msource |-> "s1", mdest |-> "s3"] \in DOMAIN messages
  \* /\ messages[[mtype |-> "RequestVoteResponse", mterm |-> 1, mvoteGranted |-> TRUE, msource |-> "s1", mdest |-> "s3"]] = 1

TargetLength == ~
  TLCGet("level") > 10

\* TargetReceive == ~
\*   /\ TLCGet("level") > 4 => Cardinality(s1Inbox) > 0
\*   /\ TLCGet("level") > 10 => Cardinality(s1Inbox) = 0

TargetSomeLeader == ~
  \E n \in Server : state[n] = "Leader"

TargetActions1 == ~
  /\ Len(actions) = 3
  /\ actions[1][1] = "Initialize"
  /\ actions[2][1] = "Timeout"
  /\ actions[3][1] = "SelfVote"

TargetActions == ~
  /\ \E n \in Server : state[n] = "Leader"
  /\ IsPrefix(<<
      "Timeout"
    , "RequestVote"
    , "RequestVote"
    , "Network"
    \* , "UpdateTerm"
    \* , "Network"
    \* , "HandleRequestVoteRequest"
    \* , "Network"
    \* , "UpdateTerm"
    \* , "HandleRequestVoteRequest"
    \* , "Network"
    \* , "RequestVote"
    \* , "RequestVote"
    \* , "HandleRequestVoteResponse"
    \* , "BecomeLeader"
    >>, actions)

Bindings(f) == SetToSeq({ <<k, f[k]>> : k \in DOMAIN f })

Post ==
    LET t1 == ToTrace(CounterExample) IN
    \* LET t2 == [ i \in 1 .. Len(t1) |->
    \*   [t1[i] EXCEPT !["messages"] = Bindings(t1[i]["messages"])] ]
    \* IN
    \* /\ PrintT(t1)
    \* /\ PrintT(t2)
    /\ JsonSerialize("trace.json", t1)
    \* /\ PrintT("using post")

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
