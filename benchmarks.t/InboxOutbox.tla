---------------------------- MODULE InboxOutbox --------------------------

\* A network model for MBTC, with the property that local communication can be observed using local variables only

EXTENDS Monitoring

VARIABLES outbox, inbox
VARIABLES inflight
CONSTANT Server

MsgsIn(box) == FoldSeq(LAMBDA c,t: box[c] \o t, <<>>, SetToSeq(Server))

SendM(sender, m) ==
  /\ \A i \in 1..Len(inflight) : inflight[i] /= m
  /\ \A i \in 1..Len(outbox[sender]) : outbox[sender][i] /= m
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

NetworkTakeMessage(sender) ==
  /\ outbox[sender] /= <<>>
  /\ outbox' = [s1 \in Server |-> <<>>]
  /\ inflight' = inflight \o MsgsIn(outbox)
  /\ UNCHANGED inbox
  \* /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
  /\ LogAction(<<"NetworkTakeMessage", MsgsIn(outbox)>>)
  /\ LogActor("Network")

NetworkDeliverMessage(recipient) ==
  /\ inflight /= <<>>
  /\ \E i \in 1..Len(inflight) :
    /\ inflight[i].mdest = recipient
    /\ inbox' = [inbox EXCEPT ![recipient] = Append(inbox[recipient], inflight[i])]
    /\ inflight' = RemoveAt(inflight, i)
    /\ LogAction(<<"NetworkDeliverMessage", inflight[i]>>)
    /\ LogActor("Network")
    /\ UNCHANGED outbox
    \* /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* tractable model checking
SoupSize == Len(inflight) <= 2

=============================================================================