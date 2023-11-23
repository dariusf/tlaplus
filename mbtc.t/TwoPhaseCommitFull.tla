---------------------------- MODULE TwoPhaseCommitFull --------------------------
EXTENDS TLC, Json, TLCExt, Monitoring, Common, InboxOutbox
\* EXTENDS TLC, Json, TLCExt, Monitoring, Common, Soup

\* Extended version that refines with details that would be present in an implementation, and also uses conventions required for automating MBTC

\* has to be named this way to check refinement
CONSTANT RM

VARIABLES
  rmState,       \* rmState[r] is the local state of resource manager r.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared"
                 \* messages.
  tmCommitted    \* The sets of RMs the TM knows have committed or aborted
  , tmAborted
  , tmDecision   \* the phase and outcome of the protocol from the perspectie of the coordinator

vars == <<tmPrepared, tmCommitted, tmAborted, rmState, tmDecision>>

\* Messages ==
\*   \* sent by coordinator
\*   [type : {"Prepare"}, rm : RM] \union
\*   [type : {"Commit"}, rm : RM] \union
\*   [type : {"Abort"}, rm : RM] \union
\*   \* sent by participant
\*   [type : {"Prepared"}, rm : RM] \union
\*   [type : {"Committed"}, rm : RM] \union
\*   [type : {"Aborted"}, rm : RM]

TPTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ ToSet(tmPrepared) \subseteq RM
  /\ ToSet(tmCommitted) \subseteq RM
  /\ ToSet(tmAborted) \subseteq RM
  /\ tmDecision \in {"commit", "abort", "none"}
  \* /\ msgs \subseteq Messages

TPInit ==   
  /\ rmState = [r \in RM |-> "working"]
  /\ tmCommitted = <<>>
  /\ tmAborted = <<>>
  /\ tmPrepared = <<>>
  /\ tmDecision = "none"
  /\ InitInboxOutbox
  /\ InitMonitoring

-----------------------------------------------------------------------------

CSendPrepare(r) ==
  /\ tmDecision = "none"
  /\ ToSet(tmPrepared) /= RM \* retrying is allowed
  /\ Send([type |-> "Prepare", mdest |-> r, msource |-> "coordinator"])
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted, tmDecision>>
  /\ LogAction(<<"CSendPrepare", r>>)
  /\ LogActor("coordinator")

PHandlePrepare(r) ==
  /\ rmState[r] = "working"
  /\
    \/
      /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
      /\ Reply([type |-> "Prepared", msource |-> r, mdest |-> "coordinator"],
        [type |-> "Prepare", mdest |-> r, msource |-> "coordinator"])
    \/
      /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
      /\ Reply([type |-> "Aborted", msource |-> r, mdest |-> "coordinator"],
        [type |-> "Prepare", mdest |-> r, msource |-> "coordinator"])
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted, tmDecision>>
  /\ LogAction(<<"PHandlePrepare", r, rmState'[r]>>)
  /\ LogActor(r)

CReceivePrepare(r) ==
  /\ r \notin ToSet(tmPrepared)
  /\ Receive([type |-> "Prepared", mdest |-> "coordinator", msource |-> r])
  /\ tmPrepared' = Append(tmPrepared, r)
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmCommitted, tmAborted, tmDecision>>
  /\ LogAction(<<"CReceivePrepare", r>>)
  /\ LogActor("coordinator")

CReceiveAbort(r) ==
  /\ Receive([type |-> "Aborted", msource |-> r, mdest |-> "coordinator"])
  /\ r \notin ToSet(tmAborted)
  /\ tmAborted' = Append(tmAborted, r)
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmDecision>>
  /\ LogAction(<<"CReceiveAbort", r>>)
  /\ LogActor("coordinator")

CSendCommit(r) ==
  /\ ToSet(tmPrepared) = RM
  /\ tmDecision /= "abort"
  /\ tmDecision' = "commit"
  /\ Send([type |-> "Commit", mdest |-> r, msource |-> "coordinator"])
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>
  /\ LogAction(<<"CSendCommit", r>>)
  /\ LogActor("coordinator")

CSendAbort(r) ==
  /\ Len(tmAborted) > 0
  /\ tmDecision /= "commit"
  /\ tmDecision' = "abort"
  /\ r \notin ToSet(tmAborted)
  /\ Send([type |-> "Abort", mdest |-> r, msource |-> "coordinator"])
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>
  /\ LogAction(<<"CSendAbort", r>>)
  /\ LogActor("coordinator")

PHandleCommit(r) ==
  /\ rmState[r] = "prepared"
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ Reply([type |-> "Committed", msource |-> r, mdest |-> "coordinator"],
    [type |-> "Commit", mdest |-> r, msource |-> "coordinator"])
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted, tmDecision>>
  /\ LogAction(<<"PHandleCommit", r>>)
  /\ LogActor(r)

CReceiveCommit(r) ==
  /\ Receive([type |-> "Committed", msource |-> r, mdest |-> "coordinator"])
  /\ r \notin ToSet(tmCommitted)
  /\ tmCommitted' = Append(tmCommitted, r)
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, tmAborted, tmDecision>>
  /\ LogAction(<<"CReceiveCommit", r>>)
  /\ LogActor("coordinator")

PHandleAbort(r) ==
  /\ rmState[r] \in {"working", "prepared"}
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ Reply([type |-> "Aborted", msource |-> r, mdest |-> "coordinator"],
    [type |-> "Abort", mdest |-> r, msource |-> "coordinator"])
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted, tmDecision>>
  /\ LogAction(<<"PHandleAbort", r>>)
  /\ LogActor(r)

-----------------------------------------------------------------------------

\* CReset ==
\*   \* only read local state to determine whether to reset
\*   /\
\*     \/ \A r \in RM : [type |-> "Committed", rm |-> r] \in msgs
\*     \/ \A r \in RM : [type |-> "Aborted", rm |-> r] \in msgs
\*   /\ tmPrepared' = <<>>
\*   /\ tmCommitted' = <<>>
\*   /\ tmAborted' = <<>>
\*   /\ UNCHANGED <<rmState>>
\*   \* /\ LogAction(<<"CReset">>)
\*   \* /\ LogActor("coordinator")

\* PReset ==
\*   \* this resets several participants at once, but we're not focusing on participants for now
\*   /\
\*     \/ \A r \in RM : rmState[r] = "aborted"
\*     \/ \A r \in RM : rmState[r] = "committed"
\*   /\ rmState' = [r \in RM |-> "working"]
\*   /\ who' = "none" \* TODO
\*   /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>
\*   \* /\ LogAction(<<"PReset">>)
\*   \* /\ LogActor("participants") \* TODO

-----------------------------------------------------------------------------

TPNext ==
  \/ \E r \in RM :
    \/ CSendPrepare(r) \/ PHandlePrepare(r) \/ CReceivePrepare(r)
    \/ CSendCommit(r) \/ PHandleCommit(r) \/ CReceiveCommit(r)
    \/ CSendAbort(r) \/ PHandleAbort(r) \/ CReceiveAbort(r)
  \/ \E i \in 1..Len(inflight) :
    /\ NetworkDeliverMessage(inflight[i])
    /\ UNCHANGED vars
  \/ \E r \in RM \union {"coordinator"} : \E i \in 1..Len(outbox[r]) :
    /\ NetworkTakeMessage(outbox[r][i])
    /\ UNCHANGED vars
    
  \* \/ \E r \in (RM \union {"coordinator"}) :
  \*   /\ UNCHANGED vars
  \*   /\
  \*     \/ NetworkTakeMessage(r)
  \*     \/ NetworkDeliverMessage(r)

TPSpecF == [][TPNext]_<<vars, monitoringVars, inboxOutboxVars>> /\ TPInit

THEOREM TPSpecF => []TPTypeOK

\* this is no longer true, as we've removed some state and made changes to other things

\* TPC == INSTANCE TwoPhaseCommit WITH
\*   tmPrepared <- ToSet(tmPrepared)

\* TPCSpec == TPC!TPSpec

\* THEOREM TPSpecF => TPC!TPSpec

TC == INSTANCE TCommit

TCConsistent == TC!TCConsistent
TCSpec == TC!TCSpec

ConstrBounded == TLCGet("level") < 50

DesiredHist == <<
\* phase 1
    <<"CSendPrepare", "r1">>
    , <<"CSendPrepare", "r2">>
    , <<"NetworkTakeMessage", [type |-> "Prepare", mdest |-> "r2", msource |-> "coordinator"]>>
    , <<"NetworkTakeMessage", [type |-> "Prepare", mdest |-> "r1", msource |-> "coordinator"]>>
    , <<"NetworkDeliverMessage", [type |-> "Prepare", mdest |-> "r1", msource |-> "coordinator"]>>
    , <<"NetworkDeliverMessage", [type |-> "Prepare", mdest |-> "r2", msource |-> "coordinator"]>>
    , <<"PHandlePrepare", "r1", "prepared">>
    , <<"PHandlePrepare", "r2", "prepared">>
    , <<"NetworkTakeMessage", [type |-> "Prepared", msource |-> "r1", mdest |-> "coordinator"]>>
    , <<"NetworkTakeMessage", [type |-> "Prepared", msource |-> "r2", mdest |-> "coordinator"]>>
    , <<"NetworkDeliverMessage", [type |-> "Prepared", msource |-> "r1", mdest |-> "coordinator"]>>
    , <<"NetworkDeliverMessage", [type |-> "Prepared", msource |-> "r2", mdest |-> "coordinator"]>>
    , <<"CReceivePrepare", "r1">>
    , <<"CReceivePrepare", "r2">>

\* phase 2
    , <<"CSendCommit", "r2">>
    , <<"CSendCommit", "r1">>
    , <<"NetworkTakeMessage", [type |-> "Commit", mdest |-> "r2", msource |-> "coordinator"]>>
    , <<"NetworkTakeMessage", [type |-> "Commit", mdest |-> "r1", msource |-> "coordinator"]>>
    , <<"NetworkDeliverMessage", [type |-> "Commit", mdest |-> "r1", msource |-> "coordinator"]>>
    , <<"NetworkDeliverMessage", [type |-> "Commit", mdest |-> "r2", msource |-> "coordinator"]>>

    , <<"PHandleCommit", "r1">>
    , <<"PHandleCommit", "r2">>

    , <<"NetworkTakeMessage", [type |-> "Committed", msource |-> "r2", mdest |-> "coordinator"]>>
    , <<"NetworkTakeMessage", [type |-> "Committed", msource |-> "r1", mdest |-> "coordinator"]>>
    , <<"NetworkDeliverMessage", [type |-> "Committed", msource |-> "r1", mdest |-> "coordinator"]>>
    , <<"NetworkDeliverMessage", [type |-> "Committed", msource |-> "r2", mdest |-> "coordinator"]>>

    , <<"CReceiveCommit", "r1">>
    , <<"CReceiveCommit", "r2">>
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

TargetLength == ~
  /\ TLCGet("level") > 4

TargetInterm == ~
  /\ Len(tmCommitted) > 0
  \* /\ Len(tmPrepared) > 0

TargetCommit == ~
  /\ ToSet(tmCommitted) = RM
  /\ ~ TC!TargetCommit

TargetAbort == ~
  /\ ToSet(tmAborted) = RM
  /\ ~ TC!TargetAbort

Post ==
    LET t1 == ToTrace(CounterExample) IN
    \* LET t2 == [ i \in 1 .. Len(t1) |-> [t1[i] EXCEPT !["y"] = Bindings(t1[i]["y"])] ] IN
    /\ JsonSerialize("trace.json", t1)

\* cannot use symmetry because we can't use model values, because we're using strings for technical issues

(* Definitions for symmetry set-based reduction *)
\* CONSTANTS
\* r1, r2
\* symm == Permutations({r1, r2})

=============================================================================
