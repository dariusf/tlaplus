---------------------------- MODULE Soup --------------------------

\* A simple and efficient network model for model checking

EXTENDS Monitoring

VARIABLES msgs
CONSTANT Server

inboxOutboxVars == <<msgs>>

InitInboxOutbox ==
  /\ msgs = {}

Send(m) ==
  /\ m \notin msgs
  /\ msgs' = msgs \union {m}

Discard(m) ==
  /\ m \in msgs
  /\ msgs' = msgs \ {m}

Receive(m) == Discard(m)

Reply(res, req) ==
  /\ res \notin msgs
  /\ req \in msgs
  /\ msgs' = (msgs \union {res}) \ {req}

=============================================================================