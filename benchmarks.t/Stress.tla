---- MODULE Stress ----

EXTENDS Naturals

VARIABLE x
vars == <<x>>

Init == x = 1

A ==
  /\ x < 0
  /\ x' = x + 1

A1 ==
  /\ x < 0
  /\ x' = x + 1
    /\ x < 0

B ==
  /\ UNCHANGED x

Send(y) == x = y
C ==
  /\ Send(x)

D ==
  \/
    /\ x = 1
    /\ x' = 2
  \/
    /\ x /= 1
    /\ x' = 3

E ==
  \/
    /\ x = 1
    /\ x' = 2
    /\
      \/ x = 2
      \/
        /\ x = 3
        /\ x = 1
  \/
    /\ x /= 1
    /\ x' = 3

F(z) == TRUE

Next ==
  \/ A
  \/ A1
  \/ B
  \/ C
  \/ D
  \/ E
  \/ F(1)

Spec == Init /\ [][Next]_vars

====
