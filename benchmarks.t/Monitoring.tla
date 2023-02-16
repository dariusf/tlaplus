---------------------------- MODULE Monitoring --------------------------

EXTENDS Common

VARIABLES actions, who

monitoringVars == <<actions, who>>
InitMonitoring ==
  /\ actions = <<>>
  /\ who = "none"

LogAction(a) ==
  /\ actions' = Append(actions, a)
  \* /\ actions' = a

LogActor(w) ==
  /\ who' = w
  \* /\ who' = Append(who, w)

=============================================================================