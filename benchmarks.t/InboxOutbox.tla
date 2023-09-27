---------------------------- MODULE InboxOutbox --------------------------

\* A network model for MBTC, with the property that local communication can be observed using local variables only

EXTENDS Monitoring

VARIABLES outbox, inbox
VARIABLES inflight
CONSTANT Server

\* converts a map of id -> seq to seq
MsgsIn(box) == FoldSeq(LAMBDA c,t: box[c] \o t, <<>>, SetToSeq(Server))

SendM(sender, m) ==
  \* /\ \A i \in 1..Len(inflight) : inflight[i] /= m
  \* /\ \A i \in 1..Len(outbox[sender]) : outbox[sender][i] /= m
  /\ outbox' = [outbox EXCEPT ![sender] = Append(outbox[sender], m)]

RecvM(recipient, m) ==
  /\ m \in ToSet(inbox[recipient])
  /\ inbox' = [inbox EXCEPT ![recipient] = Remove(inbox[recipient], m)]

\* user-facing operators and definitions

inboxOutboxVars == <<inbox, outbox, inflight>>

InitInboxOutbox ==
  /\ inbox = [i \in Server |-> <<>>]
  /\ outbox = [i \in Server |-> <<>>]
  /\ inflight = <<>>

Discard(m) ==
  /\ RecvM(m.mdest, m)
  /\ UNCHANGED outbox
  /\ UNCHANGED inflight

Receive(m) == Discard(m)

Send(m) ==
  /\ SendM(m.msource, m)
  /\ UNCHANGED inflight
  /\ UNCHANGED inbox

Reply(res, req) ==
  /\ RecvM(req.mdest, req)
  /\ SendM(res.msource, res)
  /\ UNCHANGED inflight

NetworkTakeMessage(msg) ==
  /\ msg \in ToSet(outbox[msg.msource])
  /\ outbox' = [outbox EXCEPT ![msg.msource] = Remove(outbox[msg.msource], msg)]
  /\ inflight' = Append(inflight, msg)
  /\ LogAction(<<"NetworkTakeMessage", msg>>)
  /\ LogActor("Network")
  /\ UNCHANGED inbox

NetworkDeliverMessage(msg) ==
  /\ msg \in ToSet(inflight)
  /\ inflight' = Remove(inflight, msg)
  /\ inbox' = [inbox EXCEPT ![msg.mdest] = Append(inbox[msg.mdest], msg)]
  /\ LogAction(<<"NetworkDeliverMessage", msg>>)
  /\ LogActor("Network")
  /\ UNCHANGED outbox

NetworkTakeMessageProjected(msg) ==
  /\ msg \in ToSet(outbox[msg.msource])
  /\ UNCHANGED inflight
  /\ outbox' = [outbox EXCEPT ![msg.msource] = Remove(outbox[msg.msource], msg)]
  /\ LogAction(<<"NetworkTakeMessage", msg>>)
  /\ LogActor("Network")
  /\ UNCHANGED inbox

NetworkDeliverMessageProjected(msg) ==
  /\ UNCHANGED inflight
  /\ inbox' = [inbox EXCEPT ![msg.mdest] = Append(inbox[msg.mdest], msg)]
  /\ LogAction(<<"NetworkDeliverMessage", msg>>)
  /\ LogActor("Network")
  /\ UNCHANGED outbox

\* tractable model checking
SoupSize ==
  /\ Len(inflight) <= 3
  /\ \A s \in Server : Len(outbox[s]) <= 1
  /\ \A s \in Server : Len(inbox[s]) <= 1

=============================================================================
