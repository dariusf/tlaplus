---- MODULE Counter ----

EXTENDS Naturals

VARIABLE x
vars == <<x>>

Init == x = 1

A == x' = x + 1

Next ==
  \/ A

Spec == Init /\ [][Next]_vars

Constr == x < 2

Inv == x < 3

====
