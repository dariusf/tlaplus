---------------------------- MODULE TwoPhaseCommitFull --------------------------
EXTENDS TLC, Sequences, FiniteSets, Naturals, Json, TLCExt

ToSet(s) == { s[i] : i \in DOMAIN s }
Option(T) == Seq(T)
Some(e) == <<e>>
None == <<>>

\* Extended version that refines with details that would be present in an implementation, and also uses conventions required for automating MBTC

\* has to be named this way to check refinement
CONSTANT RM

VARIABLES
  rmState,       \* rmState[r] is the local state of resource manager r.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared"
                 \* messages.
  msgs           
  , who
  , tmCommitted \* The sets of RMs the TM knows have committed or aborted
  , tmAborted

  , lastMsgSent
  , lastMsgReceived
  \* by the coordinator, i.e. not updated on participants


Cvars == <<tmPrepared, tmCommitted, tmAborted, lastMsgSent, lastMsgReceived >>
Pvars == <<rmState>>
Gvars == <<msgs, who>>

vars == <<tmPrepared, tmCommitted, tmAborted, lastMsgSent, lastMsgReceived, rmState, msgs, who>>

Messages ==
  \* sent by coordinator
  [type : {"Prepare"}, rm : RM] \cup
  [type : {"Commit"}, rm : RM] \cup
  [type : {"Abort"}, rm : RM] \cup
  \* sent by participant
  [type : {"Prepared"}, rm : RM] \cup
  [type : {"Committed"}, rm : RM] \cup
  [type : {"Aborted"}, rm : RM]

TPTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ ToSet(tmPrepared) \subseteq RM
  /\ ToSet(tmCommitted) \subseteq RM
  /\ ToSet(tmAborted) \subseteq RM
  /\ msgs \subseteq Messages
  /\ who \in ({ "coordinator", "none" } \union RM)
  /\ lastMsgSent \in Option(Messages)
  /\ lastMsgReceived \in Option(Messages)

TPInit ==   
  /\ rmState = [r \in RM |-> "working"]
  /\ msgs = {}
  /\ who = "none"
  \* /\ tmCommitted = {}
  \* /\ tmAborted = {}
  \* /\ tmPrepared = {}
  /\ tmCommitted = <<>>
  /\ tmAborted = <<>>
  /\ tmPrepared = <<>>
  \* this is really because sets can't be represented in json/go... ugh
  /\ lastMsgSent = None
  /\ lastMsgReceived = None


Send(m) ==
  /\ m \notin msgs \* not already sent
  /\ msgs' = msgs \cup {m}

\* think of as an enabling condition, and also as an assertion that this message is present
Receive(m) ==
  /\ m \in msgs

-----------------------------------------------------------------------------
CReceivePrepare(r) ==
  /\ Receive([type |-> "Prepared", rm |-> r])
  \* /\ r \notin tmPrepared
  \* /\ tmPrepared' = tmPrepared \cup {r}
  /\ r \notin ToSet(tmPrepared)
  /\ tmPrepared' = Append(tmPrepared, r)
  /\ who' = "coordinator"
  /\ lastMsgReceived' = Some([type |-> "Prepared", rm |-> r])
  /\ lastMsgSent' = None
  /\ UNCHANGED <<msgs>>
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmCommitted, tmAborted>>

CSendPrepare(r) ==
  /\ ToSet(tmPrepared) /= RM \* not already received
  /\ Send([type |-> "Prepare", rm |-> r])
  /\ who' = "coordinator"
  /\ lastMsgReceived' = None
  /\ lastMsgSent' = Some([type |-> "Prepare", rm |-> r])
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>

CSendCommit(r) ==
  /\ ToSet(tmPrepared) = RM
  \* /\ tmAborted = {}
  /\ Send([type |-> "Commit", rm |-> r])
  /\ who' = "coordinator"
  /\ lastMsgReceived' = None
  /\ lastMsgSent' = Some([type |-> "Commit", rm |-> r])
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>

CSendAbort(r) ==
  \* /\ tmAborted /= {}
  /\ tmAborted /= <<>>
  /\ Send([type |-> "Abort", rm |-> r])
  /\ who' = "coordinator"
  /\ lastMsgReceived' = None
  /\ lastMsgSent' = Some([type |-> "Abort", rm |-> r])
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>

CReceiveCommit(r) ==
  /\ Receive([type |-> "Committed", rm |-> r])
  /\ r \notin ToSet(tmCommitted)
  /\ who' = "coordinator"
  \* /\ tmCommitted' = tmCommitted \cup {r}
  /\ tmCommitted' = Append(tmCommitted, r)
  /\ lastMsgReceived' = Some([type |-> "Committed", rm |-> r])
  /\ lastMsgSent' = None
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, msgs, tmAborted>>

CReceiveAbort(r) ==
  /\ Receive([type |-> "Aborted", rm |-> r])
  /\ r \notin ToSet(tmAborted)
  /\ who' = "coordinator"
  \* /\ tmAborted' = tmAborted \cup {r}
  /\ tmAborted' = Append(tmAborted, r)
  /\ lastMsgReceived' = Some([type |-> "Aborted", rm |-> r])
  /\ lastMsgSent' = None
  /\ UNCHANGED <<rmState>>
  /\ UNCHANGED <<tmPrepared, msgs, tmCommitted>>

-----------------------------------------------------------------------------

PHandlePrepare(r) == 
  /\ rmState[r] = "working"
  /\ Receive([type |-> "Prepare", rm |-> r])
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ Send([type |-> "Prepared", rm |-> r])
  /\ who' = r
  \* don't update
  \* /\ lastMsgReceived' = Some([type |-> "Prepare", rm |-> r])
  \* /\ lastMsgSent' = Some([type |-> "Prepared", rm |-> r])
  /\ UNCHANGED <<lastMsgReceived, lastMsgSent>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>

PHandleCommit(r) ==
  /\ rmState[r] = "prepared"
  /\ Receive([type |-> "Commit", rm |-> r])
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ Send([type |-> "Committed", rm |-> r])
  /\ who' = r
  \* don't update
  \* /\ lastMsgReceived' = Some([type |-> "Commit", rm |-> r])
  \* /\ lastMsgSent' = Some([type |-> "Committed", rm |-> r])
  /\ UNCHANGED <<lastMsgReceived, lastMsgSent>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>

PHandleAbort(r) ==
  /\ rmState[r] \in {"working", "prepared"}
  /\ Receive([type |-> "Abort", rm |-> r])
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ who' = r
  /\ Send([type |-> "Aborted", rm |-> r])
  \* don't update
  \* /\ lastMsgReceived' = Some([type |-> "Abort", rm |-> r])
  \* /\ lastMsgSent' = Some([type |-> "Aborted", rm |-> r])
  /\ UNCHANGED <<lastMsgReceived, lastMsgSent>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>

PSpontaneouslyAbort(r) ==
  /\ rmState[r] \in {"working", "prepared"}
  \* /\ Receive([type |-> "Abort", rm |-> r])
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ who' = r
  /\ Send([type |-> "Aborted", rm |-> r])
  \* don't update
  \* /\ lastMsgReceived' = Some([type |-> "Abort", rm |-> r])
  \* /\ lastMsgSent' = Some([type |-> "Aborted", rm |-> r])
  /\ UNCHANGED <<lastMsgReceived, lastMsgSent>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>

-----------------------------------------------------------------------------

CReset ==
  \* only read local state to determine whether to reset
  /\
    \/ \A r \in RM : [type |-> "Committed", rm |-> r] \in msgs
    \/ \A r \in RM : [type |-> "Aborted", rm |-> r] \in msgs
  /\ lastMsgReceived' = None
  /\ lastMsgSent' = None
  /\ tmPrepared' = <<>>
  /\ tmCommitted' = <<>>
  /\ tmAborted' = <<>>
  /\ msgs' = {}
  /\ UNCHANGED <<rmState>>

PReset ==
  \* this resets several participants at once, but we're not focusing on participants for now
  /\
    \/ \A r \in RM : rmState[r] = "aborted"
    \/ \A r \in RM : rmState[r] = "committed"
  /\ rmState' = [r \in RM |-> "working"]
  /\ who' = "none" \* TODO
  /\ UNCHANGED <<lastMsgReceived, lastMsgSent>>
  /\ UNCHANGED <<tmPrepared, tmCommitted, tmAborted>>
  /\ UNCHANGED <<msgs>>

\* RMChooseToAbort(r) ==
\*   /\ rmState[r] = "working"
\*   /\ [type |-> "Prepare", rm |-> r] \in msgs
\*   /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
\*   /\ msgs' = msgs \cup {[type |-> "Aborted", rm |-> r]}
\*   /\ who' = r
\*   /\ UNCHANGED <<tmPrepared, msgs, tmCommitted, tmAborted>>
\*   \* Question: why this is okay for consistency?

-----------------------------------------------------------------------------

TPNext == \E r \in RM :
  \/ CSendPrepare(r) \/ PHandlePrepare(r) \/ CReceivePrepare(r)
  \/ CSendCommit(r) \/ PHandleCommit(r) \/ CReceiveCommit(r)
  \/ CSendAbort(r) \/ PHandleAbort(r) \/ CReceiveAbort(r)
  \* \/ RMChooseToAbort(r)
  \* \/ PReset
  \* \/ CReset

TPSpecF == [][TPNext]_<<vars>> /\ TPInit

THEOREM TPSpecF => []TPTypeOK

\* this is no longer true, as we've removed some state and made changes to other things

\* TPC == INSTANCE TwoPhaseCommit WITH
\*   tmPrepared <- ToSet(tmPrepared)

\* TPCSpec == TPC!TPSpec

\* THEOREM TPSpecF => TPC!TPSpec

TC == INSTANCE TCommit

TCConsistent == TC!TCConsistent
TCSpec == TC!TCSpec

\* SuccessMessages == {"Prepare", "Prepared", "Commit", "Committed"}
\* AllMessages == SuccessMessages \cup {"Abort", "Aborted"}

\* tractable model checking
SoupSize ==
  TRUE
  \* Cardinality(msgs) <= 8
  \* \A mt \in SuccessMessages :
  \*   Cardinality({ m \in msgs : m["type"] = mt }) <= 2

TargetLength == ~
  TLCGet("level") > 15

TargetA == ~
  /\ Len(tmPrepared) = 1
  /\ Cardinality({m \in msgs : m["type"] = "Prepare"}) = 2
  \* /\ Cardinality(msgs) = 2

ConstrB ==
  /\ TLCGet("level") = 2 => lastMsgSent = Some([type |-> "Prepare", rm |-> "r2"])
  /\ TLCGet("level") = 3 => lastMsgSent = Some([type |-> "Prepare", rm |-> "r1"])
  /\ TLCGet("level") = 4 => who = "r2"
  \* this seems to be ignored on the final invariant-violating state
  /\ TLCGet("level") = 5 => FALSE

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
    \* /\ PrintT("using post")

\* cannot use symmetry because we can't use model values, because we're using strings for technical issues

(* Definitions for symmetry set-based reduction *)
\* CONSTANTS
\* r1, r2
\* symm == Permutations({r1, r2})

=============================================================================
